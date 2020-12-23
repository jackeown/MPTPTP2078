%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:55 EST 2020

% Result     : Timeout 58.83s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :  344 (2704 expanded)
%              Number of clauses        :  271 (1129 expanded)
%              Number of leaves         :   25 ( 516 expanded)
%              Depth                    :   35
%              Number of atoms          : 1016 (13246 expanded)
%              Number of equality atoms :  633 (4512 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f15])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f18,conjecture,(
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

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f47,plain,
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

fof(f48,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f41,f47])).

fof(f77,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f48])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f76,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f42])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f82,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f51])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f79,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f48])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f78,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f75,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f1,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f49,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f80,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f48])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_334,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_97556,plain,
    ( X0 != X1
    | X0 = sK2
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_334])).

cnf(c_137476,plain,
    ( X0 != k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | X0 = sK2
    | sK2 != k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_97556])).

cnf(c_205314,plain,
    ( k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) = sK2
    | sK2 != k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_137476])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_120147,plain,
    ( ~ m1_subset_1(k2_partfun1(X0,sK1,X1,sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | k1_relset_1(X2,X3,k2_partfun1(X0,sK1,X1,sK2)) = k1_relat_1(k2_partfun1(X0,sK1,X1,sK2)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_165443,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) = k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_120147])).

cnf(c_20,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_103391,plain,
    ( v1_funct_2(X0,X1,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | k1_relset_1(X1,sK1,X0) != X1
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_156776,plain,
    ( v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_103391])).

cnf(c_14,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_114598,plain,
    ( v5_relat_1(k2_partfun1(sK0,sK1,sK3,sK2),sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_136856,plain,
    ( v5_relat_1(k2_partfun1(sK0,sK1,sK3,sK2),sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_114598])).

cnf(c_102092,plain,
    ( X0 != X1
    | X0 = k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != X1 ),
    inference(instantiation,[status(thm)],[c_334])).

cnf(c_110292,plain,
    ( X0 = k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | X0 != k1_relat_1(k7_relat_1(sK3,sK2))
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != k1_relat_1(k7_relat_1(sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_102092])).

cnf(c_124362,plain,
    ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != k1_relat_1(k7_relat_1(sK3,sK2))
    | sK2 = k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | sK2 != k1_relat_1(k7_relat_1(sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_110292])).

cnf(c_335,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_114581,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK0,k1_xboole_0)
    | sK0 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_335])).

cnf(c_114583,plain,
    ( r1_tarski(sK0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | sK0 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_114581])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_974,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_988,plain,
    ( v5_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2931,plain,
    ( v5_relat_1(sK3,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_974,c_988])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_980,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2879,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | sK1 = k1_xboole_0
    | v1_funct_2(sK3,sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_974,c_980])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_33,plain,
    ( v1_funct_2(sK3,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_3568,plain,
    ( sK1 = k1_xboole_0
    | k1_relset_1(sK0,sK1,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2879,c_33])).

cnf(c_3569,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_3568])).

cnf(c_987,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3117,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_974,c_987])).

cnf(c_3570,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3569,c_3117])).

cnf(c_8,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_994,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_16,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_986,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_5249,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_986])).

cnf(c_9816,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_994,c_5249])).

cnf(c_49910,plain,
    ( sK1 = k1_xboole_0
    | v5_relat_1(sK3,X0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3570,c_9816])).

cnf(c_5,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2590,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2591,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2590])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_996,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5250,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_986,c_996])).

cnf(c_26783,plain,
    ( r1_tarski(X0,k1_xboole_0) = iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_5250])).

cnf(c_27504,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | r1_tarski(X0,k1_xboole_0) = iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_994,c_26783])).

cnf(c_44606,plain,
    ( sK1 = k1_xboole_0
    | v5_relat_1(sK3,X0) != iProver_top
    | r1_tarski(sK3,k1_xboole_0) = iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3570,c_27504])).

cnf(c_34,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_27,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_3,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_103,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_104,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1275,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1276,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1275])).

cnf(c_1305,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_334])).

cnf(c_1306,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1305])).

cnf(c_1375,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[status(thm)],[c_6,c_29])).

cnf(c_1376,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1375])).

cnf(c_333,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1485,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_333])).

cnf(c_1799,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_333])).

cnf(c_1855,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK1) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1757,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK3,k1_xboole_0)
    | sK3 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_335])).

cnf(c_2796,plain,
    ( ~ r1_tarski(sK3,X0)
    | r1_tarski(sK3,k1_xboole_0)
    | sK3 != sK3
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1757])).

cnf(c_4678,plain,
    ( ~ r1_tarski(sK3,k2_zfmisc_1(X0,sK1))
    | r1_tarski(sK3,k1_xboole_0)
    | sK3 != sK3
    | k1_xboole_0 != k2_zfmisc_1(X0,sK1) ),
    inference(instantiation,[status(thm)],[c_2796])).

cnf(c_4680,plain,
    ( sK3 != sK3
    | k1_xboole_0 != k2_zfmisc_1(X0,sK1)
    | r1_tarski(sK3,k2_zfmisc_1(X0,sK1)) != iProver_top
    | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4678])).

cnf(c_4682,plain,
    ( sK3 != sK3
    | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)
    | r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,sK1)) != iProver_top
    | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4680])).

cnf(c_336,plain,
    ( X0 != X1
    | X2 != X3
    | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
    theory(equality)).

cnf(c_8915,plain,
    ( X0 != sK1
    | X1 != sK0
    | k2_zfmisc_1(X1,X0) = k2_zfmisc_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_336])).

cnf(c_20673,plain,
    ( X0 != sK0
    | k2_zfmisc_1(X0,sK1) = k2_zfmisc_1(sK0,sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_8915])).

cnf(c_20674,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK1) = k2_zfmisc_1(sK0,sK1)
    | sK1 != sK1
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_20673])).

cnf(c_1640,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k2_zfmisc_1(X3,X4))
    | X2 != X0
    | k2_zfmisc_1(X3,X4) != X1 ),
    inference(instantiation,[status(thm)],[c_335])).

cnf(c_2392,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k2_zfmisc_1(X3,sK1))
    | X2 != X0
    | k2_zfmisc_1(X3,sK1) != X1 ),
    inference(instantiation,[status(thm)],[c_1640])).

cnf(c_4679,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK3,k2_zfmisc_1(X2,sK1))
    | k2_zfmisc_1(X2,sK1) != X1
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_2392])).

cnf(c_13118,plain,
    ( ~ r1_tarski(sK3,X0)
    | r1_tarski(sK3,k2_zfmisc_1(X1,sK1))
    | k2_zfmisc_1(X1,sK1) != X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_4679])).

cnf(c_21015,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(X0,sK1))
    | ~ r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
    | k2_zfmisc_1(X0,sK1) != k2_zfmisc_1(sK0,sK1)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_13118])).

cnf(c_21016,plain,
    ( k2_zfmisc_1(X0,sK1) != k2_zfmisc_1(sK0,sK1)
    | sK3 != sK3
    | r1_tarski(sK3,k2_zfmisc_1(X0,sK1)) = iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21015])).

cnf(c_21018,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK1) != k2_zfmisc_1(sK0,sK1)
    | sK3 != sK3
    | r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,sK1)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_21016])).

cnf(c_49743,plain,
    ( k2_zfmisc_1(X0,sK1) != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = k2_zfmisc_1(X0,sK1) ),
    inference(instantiation,[status(thm)],[c_334])).

cnf(c_49744,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK1) != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK1)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_49743])).

cnf(c_58097,plain,
    ( r1_tarski(sK0,k1_xboole_0) != iProver_top
    | r1_tarski(sK3,k1_xboole_0) = iProver_top
    | v5_relat_1(sK3,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_44606,c_34,c_27,c_103,c_104,c_1276,c_1306,c_1376,c_1485,c_1799,c_1855,c_4682,c_20674,c_21018,c_49744])).

cnf(c_58098,plain,
    ( v5_relat_1(sK3,X0) != iProver_top
    | r1_tarski(sK3,k1_xboole_0) = iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_58097])).

cnf(c_58558,plain,
    ( r1_tarski(sK0,k1_xboole_0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | v5_relat_1(sK3,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_49910,c_2591,c_58098])).

cnf(c_58559,plain,
    ( v5_relat_1(sK3,X0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_58558])).

cnf(c_58565,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2931,c_58559])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_979,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2930,plain,
    ( v5_relat_1(k2_partfun1(X0,X1,X2,X3),X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_979,c_988])).

cnf(c_28,negated_conjecture,
    ( r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_975,plain,
    ( r1_tarski(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_990,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4435,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3570,c_990])).

cnf(c_4705,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | sK1 = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4435,c_34,c_1276])).

cnf(c_4706,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4705])).

cnf(c_4715,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_975,c_4706])).

cnf(c_989,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2138,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_974,c_989])).

cnf(c_10,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_992,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_993,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4753,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK2) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4715,c_990])).

cnf(c_4848,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_993,c_4753])).

cnf(c_5031,plain,
    ( r1_tarski(X0,sK2) != iProver_top
    | sK1 = k1_xboole_0
    | k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4848,c_34,c_1276])).

cnf(c_5032,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5031])).

cnf(c_5041,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),k1_relat_1(k7_relat_1(X0,sK2)))) = k1_relat_1(k7_relat_1(X0,sK2))
    | sK1 = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_992,c_5032])).

cnf(c_11771,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),k1_relat_1(k7_relat_1(sK3,sK2)))) = k1_relat_1(k7_relat_1(sK3,sK2))
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2138,c_5041])).

cnf(c_11806,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4715,c_11771])).

cnf(c_12047,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,k1_relat_1(k7_relat_1(sK3,sK2))) != iProver_top
    | v1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11806,c_990])).

cnf(c_12938,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),k2_relat_1(X0))) = k2_relat_1(X0)
    | sK1 = k1_xboole_0
    | v5_relat_1(X0,k1_relat_1(k7_relat_1(sK3,sK2))) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_994,c_12047])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1456,plain,
    ( ~ r1_tarski(sK3,k1_xboole_0)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1351,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_1472,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_1351])).

cnf(c_1474,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(sK0,sK1,sK3,k1_xboole_0) = k7_relat_1(sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1472])).

cnf(c_1397,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k2_zfmisc_1(sK2,sK1))
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k2_zfmisc_1(sK2,sK1) != X1 ),
    inference(instantiation,[status(thm)],[c_335])).

cnf(c_1767,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(sK2,sK1))
    | r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k2_zfmisc_1(sK2,sK1))
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k2_zfmisc_1(sK2,sK1) != k2_zfmisc_1(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_1397])).

cnf(c_1770,plain,
    ( r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k2_zfmisc_1(sK2,sK1))
    | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(sK2,sK1))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | k2_zfmisc_1(sK2,sK1) != k2_zfmisc_1(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_1767])).

cnf(c_1768,plain,
    ( k2_zfmisc_1(sK2,sK1) = k2_zfmisc_1(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_333])).

cnf(c_997,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_26,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_976,plain,
    ( v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2117,plain,
    ( v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) != iProver_top
    | r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k2_zfmisc_1(sK2,sK1)) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_997,c_976])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_978,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1406,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_974,c_978])).

cnf(c_32,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_1542,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1406,c_32])).

cnf(c_2418,plain,
    ( v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) != iProver_top
    | r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k2_zfmisc_1(sK2,sK1)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2117,c_1542])).

cnf(c_2419,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k2_zfmisc_1(sK2,sK1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2418])).

cnf(c_2828,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_333])).

cnf(c_2343,plain,
    ( X0 != X1
    | X0 = k2_partfun1(sK0,sK1,sK3,X2)
    | k2_partfun1(sK0,sK1,sK3,X2) != X1 ),
    inference(instantiation,[status(thm)],[c_334])).

cnf(c_3026,plain,
    ( X0 = k2_partfun1(sK0,sK1,sK3,X1)
    | X0 != k7_relat_1(sK3,X1)
    | k2_partfun1(sK0,sK1,sK3,X1) != k7_relat_1(sK3,X1) ),
    inference(instantiation,[status(thm)],[c_2343])).

cnf(c_3027,plain,
    ( k2_partfun1(sK0,sK1,sK3,k1_xboole_0) != k7_relat_1(sK3,k1_xboole_0)
    | k1_xboole_0 = k2_partfun1(sK0,sK1,sK3,k1_xboole_0)
    | k1_xboole_0 != k7_relat_1(sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3026])).

cnf(c_4214,plain,
    ( ~ r1_tarski(k7_relat_1(sK3,X0),k1_xboole_0)
    | k1_xboole_0 = k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_4215,plain,
    ( k1_xboole_0 = k7_relat_1(sK3,X0)
    | r1_tarski(k7_relat_1(sK3,X0),k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4214])).

cnf(c_4217,plain,
    ( k1_xboole_0 = k7_relat_1(sK3,k1_xboole_0)
    | r1_tarski(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4215])).

cnf(c_4681,plain,
    ( ~ r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,sK1))
    | r1_tarski(sK3,k1_xboole_0)
    | sK3 != sK3
    | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) ),
    inference(instantiation,[status(thm)],[c_4678])).

cnf(c_5861,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) = k2_partfun1(sK0,sK1,sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_333])).

cnf(c_2830,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_334])).

cnf(c_5881,plain,
    ( X0 != sK2
    | sK2 = X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2830])).

cnf(c_5882,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_5881])).

cnf(c_6046,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_333])).

cnf(c_14498,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_21017,plain,
    ( ~ r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
    | r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,sK1))
    | k2_zfmisc_1(k1_xboole_0,sK1) != k2_zfmisc_1(sK0,sK1)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_21015])).

cnf(c_2684,plain,
    ( X0 != X1
    | k2_partfun1(sK0,sK1,sK3,sK2) != X1
    | k2_partfun1(sK0,sK1,sK3,sK2) = X0 ),
    inference(instantiation,[status(thm)],[c_334])).

cnf(c_5860,plain,
    ( X0 != k2_partfun1(sK0,sK1,sK3,sK2)
    | k2_partfun1(sK0,sK1,sK3,sK2) = X0
    | k2_partfun1(sK0,sK1,sK3,sK2) != k2_partfun1(sK0,sK1,sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_2684])).

cnf(c_14487,plain,
    ( k2_partfun1(X0,sK1,sK3,X1) != k2_partfun1(sK0,sK1,sK3,sK2)
    | k2_partfun1(sK0,sK1,sK3,sK2) = k2_partfun1(X0,sK1,sK3,X1)
    | k2_partfun1(sK0,sK1,sK3,sK2) != k2_partfun1(sK0,sK1,sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_5860])).

cnf(c_25843,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) != k2_partfun1(sK0,sK1,sK3,sK2)
    | k2_partfun1(sK0,sK1,sK3,sK2) = k2_partfun1(sK0,sK1,sK3,X0)
    | k2_partfun1(sK0,sK1,sK3,sK2) != k2_partfun1(sK0,sK1,sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_14487])).

cnf(c_25845,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k2_partfun1(sK0,sK1,sK3,sK2)
    | k2_partfun1(sK0,sK1,sK3,sK2) = k2_partfun1(sK0,sK1,sK3,k1_xboole_0)
    | k2_partfun1(sK0,sK1,sK3,k1_xboole_0) != k2_partfun1(sK0,sK1,sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_25843])).

cnf(c_343,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | k2_partfun1(X0,X2,X4,X6) = k2_partfun1(X1,X3,X5,X7) ),
    theory(equality)).

cnf(c_2346,plain,
    ( X0 != X1
    | X2 != sK3
    | X3 != sK1
    | X4 != sK0
    | k2_partfun1(X4,X3,X2,X0) = k2_partfun1(sK0,sK1,sK3,X1) ),
    inference(instantiation,[status(thm)],[c_343])).

cnf(c_3089,plain,
    ( X0 != X1
    | X2 != sK3
    | X3 != sK0
    | k2_partfun1(X3,sK1,X2,X0) = k2_partfun1(sK0,sK1,sK3,X1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2346])).

cnf(c_6158,plain,
    ( X0 != X1
    | X2 != sK0
    | k2_partfun1(X2,sK1,sK3,X0) = k2_partfun1(sK0,sK1,sK3,X1)
    | sK3 != sK3
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_3089])).

cnf(c_10511,plain,
    ( X0 != X1
    | k2_partfun1(sK0,sK1,sK3,X0) = k2_partfun1(sK0,sK1,sK3,X1)
    | sK3 != sK3
    | sK1 != sK1
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_6158])).

cnf(c_25844,plain,
    ( X0 != sK2
    | k2_partfun1(sK0,sK1,sK3,X0) = k2_partfun1(sK0,sK1,sK3,sK2)
    | sK3 != sK3
    | sK1 != sK1
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_10511])).

cnf(c_25846,plain,
    ( k2_partfun1(sK0,sK1,sK3,k1_xboole_0) = k2_partfun1(sK0,sK1,sK3,sK2)
    | sK3 != sK3
    | sK1 != sK1
    | sK0 != sK0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_25844])).

cnf(c_977,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_6752,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_974,c_977])).

cnf(c_6820,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6752,c_31,c_29,c_1472])).

cnf(c_6854,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6820,c_979])).

cnf(c_7147,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6854,c_32,c_34])).

cnf(c_7160,plain,
    ( v5_relat_1(k7_relat_1(sK3,X0),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_7147,c_988])).

cnf(c_999,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2249,plain,
    ( k1_relat_1(k7_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_992,c_999])).

cnf(c_2759,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2138,c_2249])).

cnf(c_44607,plain,
    ( v5_relat_1(k7_relat_1(sK3,k1_xboole_0),X0) != iProver_top
    | r1_tarski(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2759,c_27504])).

cnf(c_94,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_96,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_94])).

cnf(c_4,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_100,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_102,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_100])).

cnf(c_7158,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7147,c_989])).

cnf(c_7198,plain,
    ( v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_7158])).

cnf(c_48205,plain,
    ( v5_relat_1(k7_relat_1(sK3,k1_xboole_0),X0) != iProver_top
    | r1_tarski(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_44607,c_96,c_102,c_7198])).

cnf(c_48211,plain,
    ( r1_tarski(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7160,c_48205])).

cnf(c_342,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_1389,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | X0 != sK3
    | X2 != sK1
    | X1 != sK0 ),
    inference(instantiation,[status(thm)],[c_342])).

cnf(c_66535,plain,
    ( v1_funct_2(X0,X1,sK1)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | X0 != sK3
    | X1 != sK0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1389])).

cnf(c_66537,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | v1_funct_2(k1_xboole_0,k1_xboole_0,sK1)
    | sK1 != sK1
    | k1_xboole_0 != sK3
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_66535])).

cnf(c_3021,plain,
    ( X0 != X1
    | k2_partfun1(sK0,sK1,sK3,X2) != X1
    | k2_partfun1(sK0,sK1,sK3,X2) = X0 ),
    inference(instantiation,[status(thm)],[c_334])).

cnf(c_10512,plain,
    ( X0 != k2_partfun1(sK0,sK1,sK3,X1)
    | k2_partfun1(sK0,sK1,sK3,X2) = X0
    | k2_partfun1(sK0,sK1,sK3,X2) != k2_partfun1(sK0,sK1,sK3,X1) ),
    inference(instantiation,[status(thm)],[c_3021])).

cnf(c_81575,plain,
    ( X0 != k2_partfun1(sK0,sK1,sK3,X1)
    | k2_partfun1(sK0,sK1,sK3,sK2) = X0
    | k2_partfun1(sK0,sK1,sK3,sK2) != k2_partfun1(sK0,sK1,sK3,X1) ),
    inference(instantiation,[status(thm)],[c_10512])).

cnf(c_81576,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k2_partfun1(sK0,sK1,sK3,k1_xboole_0)
    | k2_partfun1(sK0,sK1,sK3,sK2) = k1_xboole_0
    | k1_xboole_0 != k2_partfun1(sK0,sK1,sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_81575])).

cnf(c_96507,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | r1_tarski(X0,k2_zfmisc_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_96509,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | r1_tarski(k1_xboole_0,k2_zfmisc_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_96507])).

cnf(c_97286,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_100857,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | sK2 != X1
    | sK1 != X2 ),
    inference(instantiation,[status(thm)],[c_342])).

cnf(c_105036,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | sK2 != X1
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_100857])).

cnf(c_105038,plain,
    ( v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK1)
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 != k1_xboole_0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_105036])).

cnf(c_98490,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_335])).

cnf(c_104103,plain,
    ( ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_98490])).

cnf(c_105825,plain,
    ( ~ r1_tarski(sK2,sK0)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_104103])).

cnf(c_110385,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),k2_relat_1(X0))) = k2_relat_1(X0)
    | v5_relat_1(X0,k1_relat_1(k7_relat_1(sK3,sK2))) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12938,c_31,c_30,c_29,c_28,c_27,c_103,c_104,c_1306,c_1375,c_1456,c_1474,c_1485,c_1770,c_1768,c_1799,c_1855,c_2419,c_2828,c_3027,c_4217,c_4681,c_5861,c_5882,c_6046,c_14498,c_20674,c_21017,c_25845,c_25846,c_48211,c_49744,c_66537,c_81576,c_96509,c_97286,c_105038,c_105825])).

cnf(c_7155,plain,
    ( k2_partfun1(sK0,sK1,k7_relat_1(sK3,X0),X1) = k7_relat_1(k7_relat_1(sK3,X0),X1)
    | v1_funct_1(k7_relat_1(sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7147,c_977])).

cnf(c_6827,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6820,c_1542])).

cnf(c_9176,plain,
    ( k2_partfun1(sK0,sK1,k7_relat_1(sK3,X0),X1) = k7_relat_1(k7_relat_1(sK3,X0),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7155,c_6827])).

cnf(c_1945,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_partfun1(X1,X2,X0,X3),k2_zfmisc_1(X1,X2)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_979,c_996])).

cnf(c_9428,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | r1_tarski(k7_relat_1(k7_relat_1(sK3,X0),X1),k2_zfmisc_1(sK0,sK1)) = iProver_top
    | v1_funct_1(k7_relat_1(sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9176,c_1945])).

cnf(c_10766,plain,
    ( r1_tarski(k7_relat_1(k7_relat_1(sK3,X0),X1),k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9428,c_32,c_34,c_6827,c_6854])).

cnf(c_2136,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_997,c_989])).

cnf(c_10773,plain,
    ( v1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10766,c_2136])).

cnf(c_110395,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),k2_relat_1(X0))) = k2_relat_1(X0)
    | v5_relat_1(X0,k1_relat_1(k7_relat_1(sK3,sK2))) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_110385,c_10773])).

cnf(c_110409,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),k2_relat_1(X0))) = k2_relat_1(X0)
    | sK1 = k1_xboole_0
    | v5_relat_1(X0,sK2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4715,c_110395])).

cnf(c_110950,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),k2_relat_1(X0))) = k2_relat_1(X0)
    | v5_relat_1(X0,sK2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_110409,c_31,c_30,c_29,c_28,c_27,c_103,c_104,c_1306,c_1375,c_1456,c_1474,c_1485,c_1770,c_1768,c_1799,c_1855,c_2419,c_2828,c_3027,c_4217,c_4681,c_5861,c_5882,c_6046,c_14498,c_20674,c_21017,c_25845,c_25846,c_48211,c_49744,c_66537,c_81576,c_96509,c_97286,c_105038,c_105825])).

cnf(c_110962,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),k2_relat_1(k2_partfun1(X0,sK2,X1,X2)))) = k2_relat_1(k2_partfun1(X0,sK2,X1,X2))
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(k2_partfun1(X0,sK2,X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2930,c_110950])).

cnf(c_2137,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_979,c_989])).

cnf(c_111476,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),k2_relat_1(k2_partfun1(X0,sK2,X1,X2)))) = k2_relat_1(k2_partfun1(X0,sK2,X1,X2))
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_110962,c_2137])).

cnf(c_111484,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),k2_relat_1(k2_partfun1(k1_xboole_0,sK2,X0,X1)))) = k2_relat_1(k2_partfun1(k1_xboole_0,sK2,X0,X1))
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_111476])).

cnf(c_111915,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),k2_relat_1(k2_partfun1(k1_xboole_0,sK2,sK3,X0)))) = k2_relat_1(k2_partfun1(k1_xboole_0,sK2,sK3,X0))
    | r1_tarski(sK0,k1_xboole_0) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_58565,c_111484])).

cnf(c_1459,plain,
    ( k1_xboole_0 = sK3
    | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1456])).

cnf(c_2693,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(sK0,sK1,sK3,sK2) = k7_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_1472])).

cnf(c_5862,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k2_partfun1(sK0,sK1,sK3,sK2)
    | k2_partfun1(sK0,sK1,sK3,sK2) = k1_xboole_0
    | k1_xboole_0 != k2_partfun1(sK0,sK1,sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_5860])).

cnf(c_59364,plain,
    ( r1_tarski(sK3,k1_xboole_0) = iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_58565,c_996])).

cnf(c_2724,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_partfun1(sK0,sK1,sK3,X2),k1_xboole_0)
    | k2_partfun1(sK0,sK1,sK3,X2) != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_335])).

cnf(c_6024,plain,
    ( r1_tarski(k2_partfun1(sK0,sK1,sK3,X0),k1_xboole_0)
    | ~ r1_tarski(k7_relat_1(sK3,X0),X1)
    | k2_partfun1(sK0,sK1,sK3,X0) != k7_relat_1(sK3,X0)
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_2724])).

cnf(c_9085,plain,
    ( r1_tarski(k2_partfun1(sK0,sK1,sK3,X0),k1_xboole_0)
    | ~ r1_tarski(k7_relat_1(sK3,X0),sK3)
    | k2_partfun1(sK0,sK1,sK3,X0) != k7_relat_1(sK3,X0)
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_6024])).

cnf(c_70674,plain,
    ( r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k1_xboole_0)
    | ~ r1_tarski(k7_relat_1(sK3,sK2),sK3)
    | k2_partfun1(sK0,sK1,sK3,sK2) != k7_relat_1(sK3,sK2)
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_9085])).

cnf(c_2328,plain,
    ( ~ r1_tarski(k2_partfun1(sK0,sK1,sK3,X0),k1_xboole_0)
    | k1_xboole_0 = k2_partfun1(sK0,sK1,sK3,X0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_70689,plain,
    ( ~ r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k1_xboole_0)
    | k1_xboole_0 = k2_partfun1(sK0,sK1,sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_2328])).

cnf(c_11,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_105775,plain,
    ( r1_tarski(k7_relat_1(sK3,sK2),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_106222,plain,
    ( ~ r1_tarski(sK0,k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_106223,plain,
    ( k1_xboole_0 = sK0
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_106222])).

cnf(c_112910,plain,
    ( r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_111915,c_31,c_30,c_29,c_28,c_1275,c_1459,c_1770,c_1768,c_1799,c_2419,c_2693,c_2828,c_5862,c_5861,c_5882,c_14498,c_59364,c_66537,c_70674,c_70689,c_96509,c_97286,c_105038,c_105775,c_105825,c_106223])).

cnf(c_112912,plain,
    ( ~ r1_tarski(sK0,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_112910])).

cnf(c_95751,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_334])).

cnf(c_96570,plain,
    ( X0 != sK2
    | sK2 = X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_95751])).

cnf(c_97546,plain,
    ( k1_relat_1(k7_relat_1(X0,sK2)) != sK2
    | sK2 = k1_relat_1(k7_relat_1(X0,sK2))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_96570])).

cnf(c_108505,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | sK2 = k1_relat_1(k7_relat_1(sK3,sK2))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_97546])).

cnf(c_95552,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2)
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != X0
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_335])).

cnf(c_95747,plain,
    ( ~ r1_tarski(X0,sK2)
    | r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2)
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_95552])).

cnf(c_96549,plain,
    ( ~ r1_tarski(k1_relat_1(X0),sK2)
    | r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2)
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != k1_relat_1(X0)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_95747])).

cnf(c_100165,plain,
    ( r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != k1_relat_1(k7_relat_1(sK3,sK2))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_96549])).

cnf(c_340,plain,
    ( X0 != X1
    | k1_relat_1(X0) = k1_relat_1(X1) ),
    theory(equality)).

cnf(c_96550,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) = k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_340])).

cnf(c_97967,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k7_relat_1(sK3,sK2)
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_96550])).

cnf(c_49274,plain,
    ( v1_relat_1(k7_relat_1(sK3,sK2))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_5192,plain,
    ( ~ v5_relat_1(X0,sK1)
    | r1_tarski(k2_relat_1(X0),sK1)
    | ~ v1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_24212,plain,
    ( ~ v5_relat_1(k2_partfun1(sK0,sK1,sK3,sK2),sK1)
    | r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
    | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_5192])).

cnf(c_6048,plain,
    ( X0 != X1
    | sK0 != X1
    | sK0 = X0 ),
    inference(instantiation,[status(thm)],[c_334])).

cnf(c_14842,plain,
    ( X0 != sK0
    | sK0 = X0
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_6048])).

cnf(c_14843,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_14842])).

cnf(c_12045,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) = iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11806,c_992])).

cnf(c_12073,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
    | ~ v1_relat_1(k7_relat_1(sK3,sK2))
    | sK1 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_12045])).

cnf(c_1346,plain,
    ( m1_subset_1(k2_partfun1(X0,X1,sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1531,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1346])).

cnf(c_8654,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1531])).

cnf(c_4003,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_8653,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_4003])).

cnf(c_5256,plain,
    ( v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) != iProver_top
    | r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2) != iProver_top
    | r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top
    | v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_986,c_976])).

cnf(c_3385,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2)
    | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
    | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_3386,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top
    | r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2) != iProver_top
    | r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1) != iProver_top
    | v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3385])).

cnf(c_4319,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[status(thm)],[c_24,c_29])).

cnf(c_1425,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
    | ~ v1_funct_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1406])).

cnf(c_4773,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4319,c_31,c_1425])).

cnf(c_4784,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_4773,c_26])).

cnf(c_4785,plain,
    ( v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4784])).

cnf(c_5741,plain,
    ( r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1) != iProver_top
    | r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2) != iProver_top
    | v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) != iProver_top
    | v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5256,c_3386,c_4785])).

cnf(c_5742,plain,
    ( v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) != iProver_top
    | r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2) != iProver_top
    | r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1) != iProver_top
    | v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5741])).

cnf(c_5743,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2)
    | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
    | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5742])).

cnf(c_101,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_95,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_205314,c_165443,c_156776,c_136856,c_124362,c_114583,c_112912,c_108505,c_100165,c_97967,c_49274,c_24212,c_14843,c_12073,c_8654,c_8653,c_6046,c_5743,c_4715,c_3385,c_2828,c_2693,c_1306,c_1275,c_104,c_103,c_101,c_95,c_27,c_29,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:12:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 58.83/8.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 58.83/8.00  
% 58.83/8.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 58.83/8.00  
% 58.83/8.00  ------  iProver source info
% 58.83/8.00  
% 58.83/8.00  git: date: 2020-06-30 10:37:57 +0100
% 58.83/8.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 58.83/8.00  git: non_committed_changes: false
% 58.83/8.00  git: last_make_outside_of_git: false
% 58.83/8.00  
% 58.83/8.00  ------ 
% 58.83/8.00  ------ Parsing...
% 58.83/8.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 58.83/8.00  
% 58.83/8.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 58.83/8.00  
% 58.83/8.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 58.83/8.00  
% 58.83/8.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 58.83/8.00  ------ Proving...
% 58.83/8.00  ------ Problem Properties 
% 58.83/8.00  
% 58.83/8.00  
% 58.83/8.00  clauses                                 32
% 58.83/8.00  conjectures                             6
% 58.83/8.00  EPR                                     5
% 58.83/8.00  Horn                                    27
% 58.83/8.00  unary                                   7
% 58.83/8.00  binary                                  10
% 58.83/8.00  lits                                    76
% 58.83/8.00  lits eq                                 20
% 58.83/8.00  fd_pure                                 0
% 58.83/8.00  fd_pseudo                               0
% 58.83/8.00  fd_cond                                 5
% 58.83/8.00  fd_pseudo_cond                          0
% 58.83/8.00  AC symbols                              0
% 58.83/8.00  
% 58.83/8.00  ------ Input Options Time Limit: Unbounded
% 58.83/8.00  
% 58.83/8.00  
% 58.83/8.00  ------ 
% 58.83/8.00  Current options:
% 58.83/8.00  ------ 
% 58.83/8.00  
% 58.83/8.00  
% 58.83/8.00  
% 58.83/8.00  
% 58.83/8.00  ------ Proving...
% 58.83/8.00  
% 58.83/8.00  
% 58.83/8.00  % SZS status Theorem for theBenchmark.p
% 58.83/8.00  
% 58.83/8.00  % SZS output start CNFRefutation for theBenchmark.p
% 58.83/8.00  
% 58.83/8.00  fof(f13,axiom,(
% 58.83/8.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 58.83/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 58.83/8.00  
% 58.83/8.00  fof(f31,plain,(
% 58.83/8.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 58.83/8.00    inference(ennf_transformation,[],[f13])).
% 58.83/8.00  
% 58.83/8.00  fof(f64,plain,(
% 58.83/8.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 58.83/8.00    inference(cnf_transformation,[],[f31])).
% 58.83/8.00  
% 58.83/8.00  fof(f15,axiom,(
% 58.83/8.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 58.83/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 58.83/8.00  
% 58.83/8.00  fof(f34,plain,(
% 58.83/8.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 58.83/8.00    inference(ennf_transformation,[],[f15])).
% 58.83/8.00  
% 58.83/8.00  fof(f35,plain,(
% 58.83/8.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 58.83/8.00    inference(flattening,[],[f34])).
% 58.83/8.00  
% 58.83/8.00  fof(f46,plain,(
% 58.83/8.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 58.83/8.00    inference(nnf_transformation,[],[f35])).
% 58.83/8.00  
% 58.83/8.00  fof(f68,plain,(
% 58.83/8.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 58.83/8.00    inference(cnf_transformation,[],[f46])).
% 58.83/8.00  
% 58.83/8.00  fof(f12,axiom,(
% 58.83/8.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 58.83/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 58.83/8.00  
% 58.83/8.00  fof(f20,plain,(
% 58.83/8.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 58.83/8.00    inference(pure_predicate_removal,[],[f12])).
% 58.83/8.00  
% 58.83/8.00  fof(f30,plain,(
% 58.83/8.00    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 58.83/8.00    inference(ennf_transformation,[],[f20])).
% 58.83/8.00  
% 58.83/8.00  fof(f63,plain,(
% 58.83/8.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 58.83/8.00    inference(cnf_transformation,[],[f30])).
% 58.83/8.00  
% 58.83/8.00  fof(f18,conjecture,(
% 58.83/8.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 58.83/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 58.83/8.00  
% 58.83/8.00  fof(f19,negated_conjecture,(
% 58.83/8.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 58.83/8.00    inference(negated_conjecture,[],[f18])).
% 58.83/8.00  
% 58.83/8.00  fof(f40,plain,(
% 58.83/8.00    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 58.83/8.00    inference(ennf_transformation,[],[f19])).
% 58.83/8.00  
% 58.83/8.00  fof(f41,plain,(
% 58.83/8.00    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 58.83/8.00    inference(flattening,[],[f40])).
% 58.83/8.00  
% 58.83/8.00  fof(f47,plain,(
% 58.83/8.00    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 58.83/8.00    introduced(choice_axiom,[])).
% 58.83/8.00  
% 58.83/8.00  fof(f48,plain,(
% 58.83/8.00    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 58.83/8.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f41,f47])).
% 58.83/8.00  
% 58.83/8.00  fof(f77,plain,(
% 58.83/8.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 58.83/8.00    inference(cnf_transformation,[],[f48])).
% 58.83/8.00  
% 58.83/8.00  fof(f66,plain,(
% 58.83/8.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 58.83/8.00    inference(cnf_transformation,[],[f46])).
% 58.83/8.00  
% 58.83/8.00  fof(f76,plain,(
% 58.83/8.00    v1_funct_2(sK3,sK0,sK1)),
% 58.83/8.00    inference(cnf_transformation,[],[f48])).
% 58.83/8.00  
% 58.83/8.00  fof(f6,axiom,(
% 58.83/8.00    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 58.83/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 58.83/8.00  
% 58.83/8.00  fof(f23,plain,(
% 58.83/8.00    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 58.83/8.00    inference(ennf_transformation,[],[f6])).
% 58.83/8.00  
% 58.83/8.00  fof(f45,plain,(
% 58.83/8.00    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 58.83/8.00    inference(nnf_transformation,[],[f23])).
% 58.83/8.00  
% 58.83/8.00  fof(f56,plain,(
% 58.83/8.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 58.83/8.00    inference(cnf_transformation,[],[f45])).
% 58.83/8.00  
% 58.83/8.00  fof(f2,axiom,(
% 58.83/8.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 58.83/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 58.83/8.00  
% 58.83/8.00  fof(f42,plain,(
% 58.83/8.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 58.83/8.00    inference(nnf_transformation,[],[f2])).
% 58.83/8.00  
% 58.83/8.00  fof(f43,plain,(
% 58.83/8.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 58.83/8.00    inference(flattening,[],[f42])).
% 58.83/8.00  
% 58.83/8.00  fof(f51,plain,(
% 58.83/8.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 58.83/8.00    inference(cnf_transformation,[],[f43])).
% 58.83/8.00  
% 58.83/8.00  fof(f82,plain,(
% 58.83/8.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 58.83/8.00    inference(equality_resolution,[],[f51])).
% 58.83/8.00  
% 58.83/8.00  fof(f14,axiom,(
% 58.83/8.00    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 58.83/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 58.83/8.00  
% 58.83/8.00  fof(f32,plain,(
% 58.83/8.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 58.83/8.00    inference(ennf_transformation,[],[f14])).
% 58.83/8.00  
% 58.83/8.00  fof(f33,plain,(
% 58.83/8.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 58.83/8.00    inference(flattening,[],[f32])).
% 58.83/8.00  
% 58.83/8.00  fof(f65,plain,(
% 58.83/8.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 58.83/8.00    inference(cnf_transformation,[],[f33])).
% 58.83/8.00  
% 58.83/8.00  fof(f4,axiom,(
% 58.83/8.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 58.83/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 58.83/8.00  
% 58.83/8.00  fof(f44,plain,(
% 58.83/8.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 58.83/8.00    inference(nnf_transformation,[],[f4])).
% 58.83/8.00  
% 58.83/8.00  fof(f55,plain,(
% 58.83/8.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 58.83/8.00    inference(cnf_transformation,[],[f44])).
% 58.83/8.00  
% 58.83/8.00  fof(f54,plain,(
% 58.83/8.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 58.83/8.00    inference(cnf_transformation,[],[f44])).
% 58.83/8.00  
% 58.83/8.00  fof(f79,plain,(
% 58.83/8.00    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 58.83/8.00    inference(cnf_transformation,[],[f48])).
% 58.83/8.00  
% 58.83/8.00  fof(f50,plain,(
% 58.83/8.00    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 58.83/8.00    inference(cnf_transformation,[],[f43])).
% 58.83/8.00  
% 58.83/8.00  fof(f11,axiom,(
% 58.83/8.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 58.83/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 58.83/8.00  
% 58.83/8.00  fof(f29,plain,(
% 58.83/8.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 58.83/8.00    inference(ennf_transformation,[],[f11])).
% 58.83/8.00  
% 58.83/8.00  fof(f62,plain,(
% 58.83/8.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 58.83/8.00    inference(cnf_transformation,[],[f29])).
% 58.83/8.00  
% 58.83/8.00  fof(f16,axiom,(
% 58.83/8.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 58.83/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 58.83/8.00  
% 58.83/8.00  fof(f36,plain,(
% 58.83/8.00    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 58.83/8.00    inference(ennf_transformation,[],[f16])).
% 58.83/8.00  
% 58.83/8.00  fof(f37,plain,(
% 58.83/8.00    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 58.83/8.00    inference(flattening,[],[f36])).
% 58.83/8.00  
% 58.83/8.00  fof(f73,plain,(
% 58.83/8.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 58.83/8.00    inference(cnf_transformation,[],[f37])).
% 58.83/8.00  
% 58.83/8.00  fof(f78,plain,(
% 58.83/8.00    r1_tarski(sK2,sK0)),
% 58.83/8.00    inference(cnf_transformation,[],[f48])).
% 58.83/8.00  
% 58.83/8.00  fof(f10,axiom,(
% 58.83/8.00    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 58.83/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 58.83/8.00  
% 58.83/8.00  fof(f27,plain,(
% 58.83/8.00    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 58.83/8.00    inference(ennf_transformation,[],[f10])).
% 58.83/8.00  
% 58.83/8.00  fof(f28,plain,(
% 58.83/8.00    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 58.83/8.00    inference(flattening,[],[f27])).
% 58.83/8.00  
% 58.83/8.00  fof(f61,plain,(
% 58.83/8.00    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 58.83/8.00    inference(cnf_transformation,[],[f28])).
% 58.83/8.00  
% 58.83/8.00  fof(f8,axiom,(
% 58.83/8.00    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 58.83/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 58.83/8.00  
% 58.83/8.00  fof(f25,plain,(
% 58.83/8.00    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 58.83/8.00    inference(ennf_transformation,[],[f8])).
% 58.83/8.00  
% 58.83/8.00  fof(f59,plain,(
% 58.83/8.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 58.83/8.00    inference(cnf_transformation,[],[f25])).
% 58.83/8.00  
% 58.83/8.00  fof(f7,axiom,(
% 58.83/8.00    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 58.83/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 58.83/8.00  
% 58.83/8.00  fof(f24,plain,(
% 58.83/8.00    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 58.83/8.00    inference(ennf_transformation,[],[f7])).
% 58.83/8.00  
% 58.83/8.00  fof(f58,plain,(
% 58.83/8.00    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 58.83/8.00    inference(cnf_transformation,[],[f24])).
% 58.83/8.00  
% 58.83/8.00  fof(f75,plain,(
% 58.83/8.00    v1_funct_1(sK3)),
% 58.83/8.00    inference(cnf_transformation,[],[f48])).
% 58.83/8.00  
% 58.83/8.00  fof(f1,axiom,(
% 58.83/8.00    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 58.83/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 58.83/8.00  
% 58.83/8.00  fof(f22,plain,(
% 58.83/8.00    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 58.83/8.00    inference(ennf_transformation,[],[f1])).
% 58.83/8.00  
% 58.83/8.00  fof(f49,plain,(
% 58.83/8.00    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 58.83/8.00    inference(cnf_transformation,[],[f22])).
% 58.83/8.00  
% 58.83/8.00  fof(f17,axiom,(
% 58.83/8.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 58.83/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 58.83/8.00  
% 58.83/8.00  fof(f38,plain,(
% 58.83/8.00    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 58.83/8.00    inference(ennf_transformation,[],[f17])).
% 58.83/8.00  
% 58.83/8.00  fof(f39,plain,(
% 58.83/8.00    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 58.83/8.00    inference(flattening,[],[f38])).
% 58.83/8.00  
% 58.83/8.00  fof(f74,plain,(
% 58.83/8.00    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 58.83/8.00    inference(cnf_transformation,[],[f39])).
% 58.83/8.00  
% 58.83/8.00  fof(f80,plain,(
% 58.83/8.00    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 58.83/8.00    inference(cnf_transformation,[],[f48])).
% 58.83/8.00  
% 58.83/8.00  fof(f72,plain,(
% 58.83/8.00    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 58.83/8.00    inference(cnf_transformation,[],[f37])).
% 58.83/8.00  
% 58.83/8.00  fof(f3,axiom,(
% 58.83/8.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 58.83/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 58.83/8.00  
% 58.83/8.00  fof(f53,plain,(
% 58.83/8.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 58.83/8.00    inference(cnf_transformation,[],[f3])).
% 58.83/8.00  
% 58.83/8.00  fof(f9,axiom,(
% 58.83/8.00    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 58.83/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 58.83/8.00  
% 58.83/8.00  fof(f26,plain,(
% 58.83/8.00    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 58.83/8.00    inference(ennf_transformation,[],[f9])).
% 58.83/8.00  
% 58.83/8.00  fof(f60,plain,(
% 58.83/8.00    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 58.83/8.00    inference(cnf_transformation,[],[f26])).
% 58.83/8.00  
% 58.83/8.00  cnf(c_334,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_97556,plain,
% 58.83/8.00      ( X0 != X1 | X0 = sK2 | sK2 != X1 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_334]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_137476,plain,
% 58.83/8.00      ( X0 != k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 58.83/8.00      | X0 = sK2
% 58.83/8.00      | sK2 != k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_97556]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_205314,plain,
% 58.83/8.00      ( k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 58.83/8.00      | k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) = sK2
% 58.83/8.00      | sK2 != k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_137476]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_15,plain,
% 58.83/8.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 58.83/8.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 58.83/8.00      inference(cnf_transformation,[],[f64]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_120147,plain,
% 58.83/8.00      ( ~ m1_subset_1(k2_partfun1(X0,sK1,X1,sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 58.83/8.00      | k1_relset_1(X2,X3,k2_partfun1(X0,sK1,X1,sK2)) = k1_relat_1(k2_partfun1(X0,sK1,X1,sK2)) ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_15]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_165443,plain,
% 58.83/8.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 58.83/8.00      | k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) = k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_120147]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_20,plain,
% 58.83/8.00      ( v1_funct_2(X0,X1,X2)
% 58.83/8.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 58.83/8.00      | k1_relset_1(X1,X2,X0) != X1
% 58.83/8.00      | k1_xboole_0 = X2 ),
% 58.83/8.00      inference(cnf_transformation,[],[f68]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_103391,plain,
% 58.83/8.00      ( v1_funct_2(X0,X1,sK1)
% 58.83/8.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 58.83/8.00      | k1_relset_1(X1,sK1,X0) != X1
% 58.83/8.00      | k1_xboole_0 = sK1 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_20]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_156776,plain,
% 58.83/8.00      ( v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
% 58.83/8.00      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 58.83/8.00      | k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 58.83/8.00      | k1_xboole_0 = sK1 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_103391]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_14,plain,
% 58.83/8.00      ( v5_relat_1(X0,X1)
% 58.83/8.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 58.83/8.00      inference(cnf_transformation,[],[f63]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_114598,plain,
% 58.83/8.00      ( v5_relat_1(k2_partfun1(sK0,sK1,sK3,sK2),sK1)
% 58.83/8.00      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_14]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_136856,plain,
% 58.83/8.00      ( v5_relat_1(k2_partfun1(sK0,sK1,sK3,sK2),sK1)
% 58.83/8.00      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_114598]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_102092,plain,
% 58.83/8.00      ( X0 != X1
% 58.83/8.00      | X0 = k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 58.83/8.00      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != X1 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_334]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_110292,plain,
% 58.83/8.00      ( X0 = k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 58.83/8.00      | X0 != k1_relat_1(k7_relat_1(sK3,sK2))
% 58.83/8.00      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != k1_relat_1(k7_relat_1(sK3,sK2)) ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_102092]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_124362,plain,
% 58.83/8.00      ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != k1_relat_1(k7_relat_1(sK3,sK2))
% 58.83/8.00      | sK2 = k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 58.83/8.00      | sK2 != k1_relat_1(k7_relat_1(sK3,sK2)) ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_110292]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_335,plain,
% 58.83/8.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 58.83/8.00      theory(equality) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_114581,plain,
% 58.83/8.00      ( ~ r1_tarski(X0,X1)
% 58.83/8.00      | r1_tarski(sK0,k1_xboole_0)
% 58.83/8.00      | sK0 != X0
% 58.83/8.00      | k1_xboole_0 != X1 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_335]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_114583,plain,
% 58.83/8.00      ( r1_tarski(sK0,k1_xboole_0)
% 58.83/8.00      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 58.83/8.00      | sK0 != k1_xboole_0
% 58.83/8.00      | k1_xboole_0 != k1_xboole_0 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_114581]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_29,negated_conjecture,
% 58.83/8.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 58.83/8.00      inference(cnf_transformation,[],[f77]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_974,plain,
% 58.83/8.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 58.83/8.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_988,plain,
% 58.83/8.00      ( v5_relat_1(X0,X1) = iProver_top
% 58.83/8.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
% 58.83/8.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_2931,plain,
% 58.83/8.00      ( v5_relat_1(sK3,sK1) = iProver_top ),
% 58.83/8.00      inference(superposition,[status(thm)],[c_974,c_988]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_22,plain,
% 58.83/8.00      ( ~ v1_funct_2(X0,X1,X2)
% 58.83/8.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 58.83/8.00      | k1_relset_1(X1,X2,X0) = X1
% 58.83/8.00      | k1_xboole_0 = X2 ),
% 58.83/8.00      inference(cnf_transformation,[],[f66]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_980,plain,
% 58.83/8.00      ( k1_relset_1(X0,X1,X2) = X0
% 58.83/8.00      | k1_xboole_0 = X1
% 58.83/8.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 58.83/8.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 58.83/8.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_2879,plain,
% 58.83/8.00      ( k1_relset_1(sK0,sK1,sK3) = sK0
% 58.83/8.00      | sK1 = k1_xboole_0
% 58.83/8.00      | v1_funct_2(sK3,sK0,sK1) != iProver_top ),
% 58.83/8.00      inference(superposition,[status(thm)],[c_974,c_980]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_30,negated_conjecture,
% 58.83/8.00      ( v1_funct_2(sK3,sK0,sK1) ),
% 58.83/8.00      inference(cnf_transformation,[],[f76]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_33,plain,
% 58.83/8.00      ( v1_funct_2(sK3,sK0,sK1) = iProver_top ),
% 58.83/8.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_3568,plain,
% 58.83/8.00      ( sK1 = k1_xboole_0 | k1_relset_1(sK0,sK1,sK3) = sK0 ),
% 58.83/8.00      inference(global_propositional_subsumption,
% 58.83/8.00                [status(thm)],
% 58.83/8.00                [c_2879,c_33]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_3569,plain,
% 58.83/8.00      ( k1_relset_1(sK0,sK1,sK3) = sK0 | sK1 = k1_xboole_0 ),
% 58.83/8.00      inference(renaming,[status(thm)],[c_3568]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_987,plain,
% 58.83/8.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 58.83/8.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 58.83/8.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_3117,plain,
% 58.83/8.00      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 58.83/8.00      inference(superposition,[status(thm)],[c_974,c_987]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_3570,plain,
% 58.83/8.00      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 58.83/8.00      inference(demodulation,[status(thm)],[c_3569,c_3117]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_8,plain,
% 58.83/8.00      ( ~ v5_relat_1(X0,X1)
% 58.83/8.00      | r1_tarski(k2_relat_1(X0),X1)
% 58.83/8.00      | ~ v1_relat_1(X0) ),
% 58.83/8.00      inference(cnf_transformation,[],[f56]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_994,plain,
% 58.83/8.00      ( v5_relat_1(X0,X1) != iProver_top
% 58.83/8.00      | r1_tarski(k2_relat_1(X0),X1) = iProver_top
% 58.83/8.00      | v1_relat_1(X0) != iProver_top ),
% 58.83/8.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_2,plain,
% 58.83/8.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 58.83/8.00      inference(cnf_transformation,[],[f82]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_16,plain,
% 58.83/8.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 58.83/8.00      | ~ r1_tarski(k1_relat_1(X0),X1)
% 58.83/8.00      | ~ r1_tarski(k2_relat_1(X0),X2)
% 58.83/8.00      | ~ v1_relat_1(X0) ),
% 58.83/8.00      inference(cnf_transformation,[],[f65]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_986,plain,
% 58.83/8.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 58.83/8.00      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 58.83/8.00      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 58.83/8.00      | v1_relat_1(X0) != iProver_top ),
% 58.83/8.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_5249,plain,
% 58.83/8.00      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 58.83/8.00      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 58.83/8.00      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 58.83/8.00      | v1_relat_1(X0) != iProver_top ),
% 58.83/8.00      inference(superposition,[status(thm)],[c_2,c_986]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_9816,plain,
% 58.83/8.00      ( v5_relat_1(X0,X1) != iProver_top
% 58.83/8.00      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 58.83/8.00      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 58.83/8.00      | v1_relat_1(X0) != iProver_top ),
% 58.83/8.00      inference(superposition,[status(thm)],[c_994,c_5249]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_49910,plain,
% 58.83/8.00      ( sK1 = k1_xboole_0
% 58.83/8.00      | v5_relat_1(sK3,X0) != iProver_top
% 58.83/8.00      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 58.83/8.00      | r1_tarski(sK0,k1_xboole_0) != iProver_top
% 58.83/8.00      | v1_relat_1(sK3) != iProver_top ),
% 58.83/8.00      inference(superposition,[status(thm)],[c_3570,c_9816]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_5,plain,
% 58.83/8.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 58.83/8.00      inference(cnf_transformation,[],[f55]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_2590,plain,
% 58.83/8.00      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
% 58.83/8.00      | ~ r1_tarski(sK3,k1_xboole_0) ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_5]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_2591,plain,
% 58.83/8.00      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 58.83/8.00      | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
% 58.83/8.00      inference(predicate_to_equality,[status(thm)],[c_2590]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_6,plain,
% 58.83/8.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 58.83/8.00      inference(cnf_transformation,[],[f54]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_996,plain,
% 58.83/8.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 58.83/8.00      | r1_tarski(X0,X1) = iProver_top ),
% 58.83/8.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_5250,plain,
% 58.83/8.00      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top
% 58.83/8.00      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 58.83/8.00      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 58.83/8.00      | v1_relat_1(X0) != iProver_top ),
% 58.83/8.00      inference(superposition,[status(thm)],[c_986,c_996]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_26783,plain,
% 58.83/8.00      ( r1_tarski(X0,k1_xboole_0) = iProver_top
% 58.83/8.00      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 58.83/8.00      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 58.83/8.00      | v1_relat_1(X0) != iProver_top ),
% 58.83/8.00      inference(superposition,[status(thm)],[c_2,c_5250]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_27504,plain,
% 58.83/8.00      ( v5_relat_1(X0,X1) != iProver_top
% 58.83/8.00      | r1_tarski(X0,k1_xboole_0) = iProver_top
% 58.83/8.00      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 58.83/8.00      | v1_relat_1(X0) != iProver_top ),
% 58.83/8.00      inference(superposition,[status(thm)],[c_994,c_26783]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_44606,plain,
% 58.83/8.00      ( sK1 = k1_xboole_0
% 58.83/8.00      | v5_relat_1(sK3,X0) != iProver_top
% 58.83/8.00      | r1_tarski(sK3,k1_xboole_0) = iProver_top
% 58.83/8.00      | r1_tarski(sK0,k1_xboole_0) != iProver_top
% 58.83/8.00      | v1_relat_1(sK3) != iProver_top ),
% 58.83/8.00      inference(superposition,[status(thm)],[c_3570,c_27504]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_34,plain,
% 58.83/8.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 58.83/8.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_27,negated_conjecture,
% 58.83/8.00      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 58.83/8.00      inference(cnf_transformation,[],[f79]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_3,plain,
% 58.83/8.00      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 58.83/8.00      | k1_xboole_0 = X0
% 58.83/8.00      | k1_xboole_0 = X1 ),
% 58.83/8.00      inference(cnf_transformation,[],[f50]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_103,plain,
% 58.83/8.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 58.83/8.00      | k1_xboole_0 = k1_xboole_0 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_3]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_104,plain,
% 58.83/8.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_2]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_13,plain,
% 58.83/8.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 58.83/8.00      | v1_relat_1(X0) ),
% 58.83/8.00      inference(cnf_transformation,[],[f62]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_1275,plain,
% 58.83/8.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 58.83/8.00      | v1_relat_1(sK3) ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_13]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_1276,plain,
% 58.83/8.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 58.83/8.00      | v1_relat_1(sK3) = iProver_top ),
% 58.83/8.00      inference(predicate_to_equality,[status(thm)],[c_1275]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_1305,plain,
% 58.83/8.00      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_334]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_1306,plain,
% 58.83/8.00      ( sK1 != k1_xboole_0
% 58.83/8.00      | k1_xboole_0 = sK1
% 58.83/8.00      | k1_xboole_0 != k1_xboole_0 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_1305]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_1375,plain,
% 58.83/8.00      ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
% 58.83/8.00      inference(resolution,[status(thm)],[c_6,c_29]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_1376,plain,
% 58.83/8.00      ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 58.83/8.00      inference(predicate_to_equality,[status(thm)],[c_1375]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_333,plain,( X0 = X0 ),theory(equality) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_1485,plain,
% 58.83/8.00      ( sK3 = sK3 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_333]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_1799,plain,
% 58.83/8.00      ( sK1 = sK1 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_333]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_1855,plain,
% 58.83/8.00      ( k2_zfmisc_1(k1_xboole_0,sK1) = k1_xboole_0 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_2]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_1757,plain,
% 58.83/8.00      ( ~ r1_tarski(X0,X1)
% 58.83/8.00      | r1_tarski(sK3,k1_xboole_0)
% 58.83/8.00      | sK3 != X0
% 58.83/8.00      | k1_xboole_0 != X1 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_335]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_2796,plain,
% 58.83/8.00      ( ~ r1_tarski(sK3,X0)
% 58.83/8.00      | r1_tarski(sK3,k1_xboole_0)
% 58.83/8.00      | sK3 != sK3
% 58.83/8.00      | k1_xboole_0 != X0 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_1757]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_4678,plain,
% 58.83/8.00      ( ~ r1_tarski(sK3,k2_zfmisc_1(X0,sK1))
% 58.83/8.00      | r1_tarski(sK3,k1_xboole_0)
% 58.83/8.00      | sK3 != sK3
% 58.83/8.00      | k1_xboole_0 != k2_zfmisc_1(X0,sK1) ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_2796]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_4680,plain,
% 58.83/8.00      ( sK3 != sK3
% 58.83/8.00      | k1_xboole_0 != k2_zfmisc_1(X0,sK1)
% 58.83/8.00      | r1_tarski(sK3,k2_zfmisc_1(X0,sK1)) != iProver_top
% 58.83/8.00      | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 58.83/8.00      inference(predicate_to_equality,[status(thm)],[c_4678]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_4682,plain,
% 58.83/8.00      ( sK3 != sK3
% 58.83/8.00      | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)
% 58.83/8.00      | r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,sK1)) != iProver_top
% 58.83/8.00      | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_4680]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_336,plain,
% 58.83/8.00      ( X0 != X1 | X2 != X3 | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
% 58.83/8.00      theory(equality) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_8915,plain,
% 58.83/8.00      ( X0 != sK1
% 58.83/8.00      | X1 != sK0
% 58.83/8.00      | k2_zfmisc_1(X1,X0) = k2_zfmisc_1(sK0,sK1) ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_336]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_20673,plain,
% 58.83/8.00      ( X0 != sK0
% 58.83/8.00      | k2_zfmisc_1(X0,sK1) = k2_zfmisc_1(sK0,sK1)
% 58.83/8.00      | sK1 != sK1 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_8915]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_20674,plain,
% 58.83/8.00      ( k2_zfmisc_1(k1_xboole_0,sK1) = k2_zfmisc_1(sK0,sK1)
% 58.83/8.00      | sK1 != sK1
% 58.83/8.00      | k1_xboole_0 != sK0 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_20673]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_1640,plain,
% 58.83/8.00      ( ~ r1_tarski(X0,X1)
% 58.83/8.00      | r1_tarski(X2,k2_zfmisc_1(X3,X4))
% 58.83/8.00      | X2 != X0
% 58.83/8.00      | k2_zfmisc_1(X3,X4) != X1 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_335]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_2392,plain,
% 58.83/8.00      ( ~ r1_tarski(X0,X1)
% 58.83/8.00      | r1_tarski(X2,k2_zfmisc_1(X3,sK1))
% 58.83/8.00      | X2 != X0
% 58.83/8.00      | k2_zfmisc_1(X3,sK1) != X1 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_1640]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_4679,plain,
% 58.83/8.00      ( ~ r1_tarski(X0,X1)
% 58.83/8.00      | r1_tarski(sK3,k2_zfmisc_1(X2,sK1))
% 58.83/8.00      | k2_zfmisc_1(X2,sK1) != X1
% 58.83/8.00      | sK3 != X0 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_2392]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_13118,plain,
% 58.83/8.00      ( ~ r1_tarski(sK3,X0)
% 58.83/8.00      | r1_tarski(sK3,k2_zfmisc_1(X1,sK1))
% 58.83/8.00      | k2_zfmisc_1(X1,sK1) != X0
% 58.83/8.00      | sK3 != sK3 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_4679]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_21015,plain,
% 58.83/8.00      ( r1_tarski(sK3,k2_zfmisc_1(X0,sK1))
% 58.83/8.00      | ~ r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
% 58.83/8.00      | k2_zfmisc_1(X0,sK1) != k2_zfmisc_1(sK0,sK1)
% 58.83/8.00      | sK3 != sK3 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_13118]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_21016,plain,
% 58.83/8.00      ( k2_zfmisc_1(X0,sK1) != k2_zfmisc_1(sK0,sK1)
% 58.83/8.00      | sK3 != sK3
% 58.83/8.00      | r1_tarski(sK3,k2_zfmisc_1(X0,sK1)) = iProver_top
% 58.83/8.00      | r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) != iProver_top ),
% 58.83/8.00      inference(predicate_to_equality,[status(thm)],[c_21015]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_21018,plain,
% 58.83/8.00      ( k2_zfmisc_1(k1_xboole_0,sK1) != k2_zfmisc_1(sK0,sK1)
% 58.83/8.00      | sK3 != sK3
% 58.83/8.00      | r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) != iProver_top
% 58.83/8.00      | r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,sK1)) = iProver_top ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_21016]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_49743,plain,
% 58.83/8.00      ( k2_zfmisc_1(X0,sK1) != X1
% 58.83/8.00      | k1_xboole_0 != X1
% 58.83/8.00      | k1_xboole_0 = k2_zfmisc_1(X0,sK1) ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_334]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_49744,plain,
% 58.83/8.00      ( k2_zfmisc_1(k1_xboole_0,sK1) != k1_xboole_0
% 58.83/8.00      | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK1)
% 58.83/8.00      | k1_xboole_0 != k1_xboole_0 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_49743]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_58097,plain,
% 58.83/8.00      ( r1_tarski(sK0,k1_xboole_0) != iProver_top
% 58.83/8.00      | r1_tarski(sK3,k1_xboole_0) = iProver_top
% 58.83/8.00      | v5_relat_1(sK3,X0) != iProver_top ),
% 58.83/8.00      inference(global_propositional_subsumption,
% 58.83/8.00                [status(thm)],
% 58.83/8.00                [c_44606,c_34,c_27,c_103,c_104,c_1276,c_1306,c_1376,
% 58.83/8.00                 c_1485,c_1799,c_1855,c_4682,c_20674,c_21018,c_49744]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_58098,plain,
% 58.83/8.00      ( v5_relat_1(sK3,X0) != iProver_top
% 58.83/8.00      | r1_tarski(sK3,k1_xboole_0) = iProver_top
% 58.83/8.00      | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 58.83/8.00      inference(renaming,[status(thm)],[c_58097]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_58558,plain,
% 58.83/8.00      ( r1_tarski(sK0,k1_xboole_0) != iProver_top
% 58.83/8.00      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 58.83/8.00      | v5_relat_1(sK3,X0) != iProver_top ),
% 58.83/8.00      inference(global_propositional_subsumption,
% 58.83/8.00                [status(thm)],
% 58.83/8.00                [c_49910,c_2591,c_58098]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_58559,plain,
% 58.83/8.00      ( v5_relat_1(sK3,X0) != iProver_top
% 58.83/8.00      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 58.83/8.00      | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 58.83/8.00      inference(renaming,[status(thm)],[c_58558]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_58565,plain,
% 58.83/8.00      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 58.83/8.00      | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 58.83/8.00      inference(superposition,[status(thm)],[c_2931,c_58559]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_23,plain,
% 58.83/8.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 58.83/8.00      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 58.83/8.00      | ~ v1_funct_1(X0) ),
% 58.83/8.00      inference(cnf_transformation,[],[f73]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_979,plain,
% 58.83/8.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 58.83/8.00      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 58.83/8.00      | v1_funct_1(X0) != iProver_top ),
% 58.83/8.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_2930,plain,
% 58.83/8.00      ( v5_relat_1(k2_partfun1(X0,X1,X2,X3),X1) = iProver_top
% 58.83/8.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 58.83/8.00      | v1_funct_1(X2) != iProver_top ),
% 58.83/8.00      inference(superposition,[status(thm)],[c_979,c_988]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_28,negated_conjecture,
% 58.83/8.00      ( r1_tarski(sK2,sK0) ),
% 58.83/8.00      inference(cnf_transformation,[],[f78]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_975,plain,
% 58.83/8.00      ( r1_tarski(sK2,sK0) = iProver_top ),
% 58.83/8.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_12,plain,
% 58.83/8.00      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 58.83/8.00      | ~ v1_relat_1(X1)
% 58.83/8.00      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 58.83/8.00      inference(cnf_transformation,[],[f61]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_990,plain,
% 58.83/8.00      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 58.83/8.00      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 58.83/8.00      | v1_relat_1(X0) != iProver_top ),
% 58.83/8.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_4435,plain,
% 58.83/8.00      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 58.83/8.00      | sK1 = k1_xboole_0
% 58.83/8.00      | r1_tarski(X0,sK0) != iProver_top
% 58.83/8.00      | v1_relat_1(sK3) != iProver_top ),
% 58.83/8.00      inference(superposition,[status(thm)],[c_3570,c_990]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_4705,plain,
% 58.83/8.00      ( r1_tarski(X0,sK0) != iProver_top
% 58.83/8.00      | sK1 = k1_xboole_0
% 58.83/8.00      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 58.83/8.00      inference(global_propositional_subsumption,
% 58.83/8.00                [status(thm)],
% 58.83/8.00                [c_4435,c_34,c_1276]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_4706,plain,
% 58.83/8.00      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 58.83/8.00      | sK1 = k1_xboole_0
% 58.83/8.00      | r1_tarski(X0,sK0) != iProver_top ),
% 58.83/8.00      inference(renaming,[status(thm)],[c_4705]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_4715,plain,
% 58.83/8.00      ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 | sK1 = k1_xboole_0 ),
% 58.83/8.00      inference(superposition,[status(thm)],[c_975,c_4706]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_989,plain,
% 58.83/8.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 58.83/8.00      | v1_relat_1(X0) = iProver_top ),
% 58.83/8.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_2138,plain,
% 58.83/8.00      ( v1_relat_1(sK3) = iProver_top ),
% 58.83/8.00      inference(superposition,[status(thm)],[c_974,c_989]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_10,plain,
% 58.83/8.00      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 58.83/8.00      inference(cnf_transformation,[],[f59]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_992,plain,
% 58.83/8.00      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
% 58.83/8.00      | v1_relat_1(X0) != iProver_top ),
% 58.83/8.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_9,plain,
% 58.83/8.00      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 58.83/8.00      inference(cnf_transformation,[],[f58]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_993,plain,
% 58.83/8.00      ( v1_relat_1(X0) != iProver_top
% 58.83/8.00      | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
% 58.83/8.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_4753,plain,
% 58.83/8.00      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),X0)) = X0
% 58.83/8.00      | sK1 = k1_xboole_0
% 58.83/8.00      | r1_tarski(X0,sK2) != iProver_top
% 58.83/8.00      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 58.83/8.00      inference(superposition,[status(thm)],[c_4715,c_990]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_4848,plain,
% 58.83/8.00      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),X0)) = X0
% 58.83/8.00      | sK1 = k1_xboole_0
% 58.83/8.00      | r1_tarski(X0,sK2) != iProver_top
% 58.83/8.00      | v1_relat_1(sK3) != iProver_top ),
% 58.83/8.00      inference(superposition,[status(thm)],[c_993,c_4753]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_5031,plain,
% 58.83/8.00      ( r1_tarski(X0,sK2) != iProver_top
% 58.83/8.00      | sK1 = k1_xboole_0
% 58.83/8.00      | k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),X0)) = X0 ),
% 58.83/8.00      inference(global_propositional_subsumption,
% 58.83/8.00                [status(thm)],
% 58.83/8.00                [c_4848,c_34,c_1276]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_5032,plain,
% 58.83/8.00      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),X0)) = X0
% 58.83/8.00      | sK1 = k1_xboole_0
% 58.83/8.00      | r1_tarski(X0,sK2) != iProver_top ),
% 58.83/8.00      inference(renaming,[status(thm)],[c_5031]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_5041,plain,
% 58.83/8.00      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),k1_relat_1(k7_relat_1(X0,sK2)))) = k1_relat_1(k7_relat_1(X0,sK2))
% 58.83/8.00      | sK1 = k1_xboole_0
% 58.83/8.00      | v1_relat_1(X0) != iProver_top ),
% 58.83/8.00      inference(superposition,[status(thm)],[c_992,c_5032]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_11771,plain,
% 58.83/8.00      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),k1_relat_1(k7_relat_1(sK3,sK2)))) = k1_relat_1(k7_relat_1(sK3,sK2))
% 58.83/8.00      | sK1 = k1_xboole_0 ),
% 58.83/8.00      inference(superposition,[status(thm)],[c_2138,c_5041]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_11806,plain,
% 58.83/8.00      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
% 58.83/8.00      | sK1 = k1_xboole_0 ),
% 58.83/8.00      inference(superposition,[status(thm)],[c_4715,c_11771]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_12047,plain,
% 58.83/8.00      ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),X0)) = X0
% 58.83/8.00      | sK1 = k1_xboole_0
% 58.83/8.00      | r1_tarski(X0,k1_relat_1(k7_relat_1(sK3,sK2))) != iProver_top
% 58.83/8.00      | v1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2)) != iProver_top ),
% 58.83/8.00      inference(superposition,[status(thm)],[c_11806,c_990]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_12938,plain,
% 58.83/8.00      ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),k2_relat_1(X0))) = k2_relat_1(X0)
% 58.83/8.00      | sK1 = k1_xboole_0
% 58.83/8.00      | v5_relat_1(X0,k1_relat_1(k7_relat_1(sK3,sK2))) != iProver_top
% 58.83/8.00      | v1_relat_1(X0) != iProver_top
% 58.83/8.00      | v1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2)) != iProver_top ),
% 58.83/8.00      inference(superposition,[status(thm)],[c_994,c_12047]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_31,negated_conjecture,
% 58.83/8.00      ( v1_funct_1(sK3) ),
% 58.83/8.00      inference(cnf_transformation,[],[f75]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_0,plain,
% 58.83/8.00      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 58.83/8.00      inference(cnf_transformation,[],[f49]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_1456,plain,
% 58.83/8.00      ( ~ r1_tarski(sK3,k1_xboole_0) | k1_xboole_0 = sK3 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_0]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_25,plain,
% 58.83/8.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 58.83/8.00      | ~ v1_funct_1(X0)
% 58.83/8.00      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 58.83/8.00      inference(cnf_transformation,[],[f74]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_1351,plain,
% 58.83/8.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 58.83/8.00      | ~ v1_funct_1(sK3)
% 58.83/8.00      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_25]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_1472,plain,
% 58.83/8.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 58.83/8.00      | ~ v1_funct_1(sK3)
% 58.83/8.00      | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_1351]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_1474,plain,
% 58.83/8.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 58.83/8.00      | ~ v1_funct_1(sK3)
% 58.83/8.00      | k2_partfun1(sK0,sK1,sK3,k1_xboole_0) = k7_relat_1(sK3,k1_xboole_0) ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_1472]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_1397,plain,
% 58.83/8.00      ( ~ r1_tarski(X0,X1)
% 58.83/8.00      | r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k2_zfmisc_1(sK2,sK1))
% 58.83/8.00      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 58.83/8.00      | k2_zfmisc_1(sK2,sK1) != X1 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_335]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_1767,plain,
% 58.83/8.00      ( ~ r1_tarski(X0,k2_zfmisc_1(sK2,sK1))
% 58.83/8.00      | r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k2_zfmisc_1(sK2,sK1))
% 58.83/8.00      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 58.83/8.00      | k2_zfmisc_1(sK2,sK1) != k2_zfmisc_1(sK2,sK1) ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_1397]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_1770,plain,
% 58.83/8.00      ( r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k2_zfmisc_1(sK2,sK1))
% 58.83/8.00      | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(sK2,sK1))
% 58.83/8.00      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 58.83/8.00      | k2_zfmisc_1(sK2,sK1) != k2_zfmisc_1(sK2,sK1) ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_1767]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_1768,plain,
% 58.83/8.00      ( k2_zfmisc_1(sK2,sK1) = k2_zfmisc_1(sK2,sK1) ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_333]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_997,plain,
% 58.83/8.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 58.83/8.00      | r1_tarski(X0,X1) != iProver_top ),
% 58.83/8.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_26,negated_conjecture,
% 58.83/8.00      ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
% 58.83/8.00      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 58.83/8.00      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 58.83/8.00      inference(cnf_transformation,[],[f80]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_976,plain,
% 58.83/8.00      ( v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) != iProver_top
% 58.83/8.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 58.83/8.00      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 58.83/8.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_2117,plain,
% 58.83/8.00      ( v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) != iProver_top
% 58.83/8.00      | r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k2_zfmisc_1(sK2,sK1)) != iProver_top
% 58.83/8.00      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 58.83/8.00      inference(superposition,[status(thm)],[c_997,c_976]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_24,plain,
% 58.83/8.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 58.83/8.00      | ~ v1_funct_1(X0)
% 58.83/8.00      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 58.83/8.00      inference(cnf_transformation,[],[f72]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_978,plain,
% 58.83/8.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 58.83/8.00      | v1_funct_1(X0) != iProver_top
% 58.83/8.00      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
% 58.83/8.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_1406,plain,
% 58.83/8.00      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 58.83/8.00      | v1_funct_1(sK3) != iProver_top ),
% 58.83/8.00      inference(superposition,[status(thm)],[c_974,c_978]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_32,plain,
% 58.83/8.00      ( v1_funct_1(sK3) = iProver_top ),
% 58.83/8.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_1542,plain,
% 58.83/8.00      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
% 58.83/8.00      inference(global_propositional_subsumption,
% 58.83/8.00                [status(thm)],
% 58.83/8.00                [c_1406,c_32]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_2418,plain,
% 58.83/8.00      ( v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) != iProver_top
% 58.83/8.00      | r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k2_zfmisc_1(sK2,sK1)) != iProver_top ),
% 58.83/8.00      inference(forward_subsumption_resolution,
% 58.83/8.00                [status(thm)],
% 58.83/8.00                [c_2117,c_1542]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_2419,plain,
% 58.83/8.00      ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
% 58.83/8.00      | ~ r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k2_zfmisc_1(sK2,sK1)) ),
% 58.83/8.00      inference(predicate_to_equality_rev,[status(thm)],[c_2418]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_2828,plain,
% 58.83/8.00      ( sK2 = sK2 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_333]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_2343,plain,
% 58.83/8.00      ( X0 != X1
% 58.83/8.00      | X0 = k2_partfun1(sK0,sK1,sK3,X2)
% 58.83/8.00      | k2_partfun1(sK0,sK1,sK3,X2) != X1 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_334]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_3026,plain,
% 58.83/8.00      ( X0 = k2_partfun1(sK0,sK1,sK3,X1)
% 58.83/8.00      | X0 != k7_relat_1(sK3,X1)
% 58.83/8.00      | k2_partfun1(sK0,sK1,sK3,X1) != k7_relat_1(sK3,X1) ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_2343]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_3027,plain,
% 58.83/8.00      ( k2_partfun1(sK0,sK1,sK3,k1_xboole_0) != k7_relat_1(sK3,k1_xboole_0)
% 58.83/8.00      | k1_xboole_0 = k2_partfun1(sK0,sK1,sK3,k1_xboole_0)
% 58.83/8.00      | k1_xboole_0 != k7_relat_1(sK3,k1_xboole_0) ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_3026]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_4214,plain,
% 58.83/8.00      ( ~ r1_tarski(k7_relat_1(sK3,X0),k1_xboole_0)
% 58.83/8.00      | k1_xboole_0 = k7_relat_1(sK3,X0) ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_0]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_4215,plain,
% 58.83/8.00      ( k1_xboole_0 = k7_relat_1(sK3,X0)
% 58.83/8.00      | r1_tarski(k7_relat_1(sK3,X0),k1_xboole_0) != iProver_top ),
% 58.83/8.00      inference(predicate_to_equality,[status(thm)],[c_4214]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_4217,plain,
% 58.83/8.00      ( k1_xboole_0 = k7_relat_1(sK3,k1_xboole_0)
% 58.83/8.00      | r1_tarski(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0) != iProver_top ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_4215]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_4681,plain,
% 58.83/8.00      ( ~ r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,sK1))
% 58.83/8.00      | r1_tarski(sK3,k1_xboole_0)
% 58.83/8.00      | sK3 != sK3
% 58.83/8.00      | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_4678]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_5861,plain,
% 58.83/8.00      ( k2_partfun1(sK0,sK1,sK3,sK2) = k2_partfun1(sK0,sK1,sK3,sK2) ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_333]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_2830,plain,
% 58.83/8.00      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_334]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_5881,plain,
% 58.83/8.00      ( X0 != sK2 | sK2 = X0 | sK2 != sK2 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_2830]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_5882,plain,
% 58.83/8.00      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_5881]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_6046,plain,
% 58.83/8.00      ( sK0 = sK0 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_333]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_14498,plain,
% 58.83/8.00      ( ~ r1_tarski(sK2,k1_xboole_0) | k1_xboole_0 = sK2 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_0]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_21017,plain,
% 58.83/8.00      ( ~ r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
% 58.83/8.00      | r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,sK1))
% 58.83/8.00      | k2_zfmisc_1(k1_xboole_0,sK1) != k2_zfmisc_1(sK0,sK1)
% 58.83/8.00      | sK3 != sK3 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_21015]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_2684,plain,
% 58.83/8.00      ( X0 != X1
% 58.83/8.00      | k2_partfun1(sK0,sK1,sK3,sK2) != X1
% 58.83/8.00      | k2_partfun1(sK0,sK1,sK3,sK2) = X0 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_334]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_5860,plain,
% 58.83/8.00      ( X0 != k2_partfun1(sK0,sK1,sK3,sK2)
% 58.83/8.00      | k2_partfun1(sK0,sK1,sK3,sK2) = X0
% 58.83/8.00      | k2_partfun1(sK0,sK1,sK3,sK2) != k2_partfun1(sK0,sK1,sK3,sK2) ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_2684]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_14487,plain,
% 58.83/8.00      ( k2_partfun1(X0,sK1,sK3,X1) != k2_partfun1(sK0,sK1,sK3,sK2)
% 58.83/8.00      | k2_partfun1(sK0,sK1,sK3,sK2) = k2_partfun1(X0,sK1,sK3,X1)
% 58.83/8.00      | k2_partfun1(sK0,sK1,sK3,sK2) != k2_partfun1(sK0,sK1,sK3,sK2) ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_5860]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_25843,plain,
% 58.83/8.00      ( k2_partfun1(sK0,sK1,sK3,X0) != k2_partfun1(sK0,sK1,sK3,sK2)
% 58.83/8.00      | k2_partfun1(sK0,sK1,sK3,sK2) = k2_partfun1(sK0,sK1,sK3,X0)
% 58.83/8.00      | k2_partfun1(sK0,sK1,sK3,sK2) != k2_partfun1(sK0,sK1,sK3,sK2) ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_14487]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_25845,plain,
% 58.83/8.00      ( k2_partfun1(sK0,sK1,sK3,sK2) != k2_partfun1(sK0,sK1,sK3,sK2)
% 58.83/8.00      | k2_partfun1(sK0,sK1,sK3,sK2) = k2_partfun1(sK0,sK1,sK3,k1_xboole_0)
% 58.83/8.00      | k2_partfun1(sK0,sK1,sK3,k1_xboole_0) != k2_partfun1(sK0,sK1,sK3,sK2) ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_25843]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_343,plain,
% 58.83/8.00      ( X0 != X1
% 58.83/8.00      | X2 != X3
% 58.83/8.00      | X4 != X5
% 58.83/8.00      | X6 != X7
% 58.83/8.00      | k2_partfun1(X0,X2,X4,X6) = k2_partfun1(X1,X3,X5,X7) ),
% 58.83/8.00      theory(equality) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_2346,plain,
% 58.83/8.00      ( X0 != X1
% 58.83/8.00      | X2 != sK3
% 58.83/8.00      | X3 != sK1
% 58.83/8.00      | X4 != sK0
% 58.83/8.00      | k2_partfun1(X4,X3,X2,X0) = k2_partfun1(sK0,sK1,sK3,X1) ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_343]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_3089,plain,
% 58.83/8.00      ( X0 != X1
% 58.83/8.00      | X2 != sK3
% 58.83/8.00      | X3 != sK0
% 58.83/8.00      | k2_partfun1(X3,sK1,X2,X0) = k2_partfun1(sK0,sK1,sK3,X1)
% 58.83/8.00      | sK1 != sK1 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_2346]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_6158,plain,
% 58.83/8.00      ( X0 != X1
% 58.83/8.00      | X2 != sK0
% 58.83/8.00      | k2_partfun1(X2,sK1,sK3,X0) = k2_partfun1(sK0,sK1,sK3,X1)
% 58.83/8.00      | sK3 != sK3
% 58.83/8.00      | sK1 != sK1 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_3089]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_10511,plain,
% 58.83/8.00      ( X0 != X1
% 58.83/8.00      | k2_partfun1(sK0,sK1,sK3,X0) = k2_partfun1(sK0,sK1,sK3,X1)
% 58.83/8.00      | sK3 != sK3
% 58.83/8.00      | sK1 != sK1
% 58.83/8.00      | sK0 != sK0 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_6158]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_25844,plain,
% 58.83/8.00      ( X0 != sK2
% 58.83/8.00      | k2_partfun1(sK0,sK1,sK3,X0) = k2_partfun1(sK0,sK1,sK3,sK2)
% 58.83/8.00      | sK3 != sK3
% 58.83/8.00      | sK1 != sK1
% 58.83/8.00      | sK0 != sK0 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_10511]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_25846,plain,
% 58.83/8.00      ( k2_partfun1(sK0,sK1,sK3,k1_xboole_0) = k2_partfun1(sK0,sK1,sK3,sK2)
% 58.83/8.00      | sK3 != sK3
% 58.83/8.00      | sK1 != sK1
% 58.83/8.00      | sK0 != sK0
% 58.83/8.00      | k1_xboole_0 != sK2 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_25844]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_977,plain,
% 58.83/8.00      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 58.83/8.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 58.83/8.00      | v1_funct_1(X2) != iProver_top ),
% 58.83/8.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_6752,plain,
% 58.83/8.00      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
% 58.83/8.00      | v1_funct_1(sK3) != iProver_top ),
% 58.83/8.00      inference(superposition,[status(thm)],[c_974,c_977]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_6820,plain,
% 58.83/8.00      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 58.83/8.00      inference(global_propositional_subsumption,
% 58.83/8.00                [status(thm)],
% 58.83/8.00                [c_6752,c_31,c_29,c_1472]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_6854,plain,
% 58.83/8.00      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 58.83/8.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 58.83/8.00      | v1_funct_1(sK3) != iProver_top ),
% 58.83/8.00      inference(superposition,[status(thm)],[c_6820,c_979]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_7147,plain,
% 58.83/8.00      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 58.83/8.00      inference(global_propositional_subsumption,
% 58.83/8.00                [status(thm)],
% 58.83/8.00                [c_6854,c_32,c_34]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_7160,plain,
% 58.83/8.00      ( v5_relat_1(k7_relat_1(sK3,X0),sK1) = iProver_top ),
% 58.83/8.00      inference(superposition,[status(thm)],[c_7147,c_988]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_999,plain,
% 58.83/8.00      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 58.83/8.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_2249,plain,
% 58.83/8.00      ( k1_relat_1(k7_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 58.83/8.00      | v1_relat_1(X0) != iProver_top ),
% 58.83/8.00      inference(superposition,[status(thm)],[c_992,c_999]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_2759,plain,
% 58.83/8.00      ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
% 58.83/8.00      inference(superposition,[status(thm)],[c_2138,c_2249]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_44607,plain,
% 58.83/8.00      ( v5_relat_1(k7_relat_1(sK3,k1_xboole_0),X0) != iProver_top
% 58.83/8.00      | r1_tarski(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0) = iProver_top
% 58.83/8.00      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 58.83/8.00      | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
% 58.83/8.00      inference(superposition,[status(thm)],[c_2759,c_27504]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_94,plain,
% 58.83/8.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 58.83/8.00      | r1_tarski(X0,X1) = iProver_top ),
% 58.83/8.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_96,plain,
% 58.83/8.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 58.83/8.00      | r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_94]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_4,plain,
% 58.83/8.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 58.83/8.00      inference(cnf_transformation,[],[f53]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_100,plain,
% 58.83/8.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 58.83/8.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_102,plain,
% 58.83/8.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_100]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_7158,plain,
% 58.83/8.00      ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 58.83/8.00      inference(superposition,[status(thm)],[c_7147,c_989]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_7198,plain,
% 58.83/8.00      ( v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = iProver_top ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_7158]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_48205,plain,
% 58.83/8.00      ( v5_relat_1(k7_relat_1(sK3,k1_xboole_0),X0) != iProver_top
% 58.83/8.00      | r1_tarski(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 58.83/8.00      inference(global_propositional_subsumption,
% 58.83/8.00                [status(thm)],
% 58.83/8.00                [c_44607,c_96,c_102,c_7198]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_48211,plain,
% 58.83/8.00      ( r1_tarski(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 58.83/8.00      inference(superposition,[status(thm)],[c_7160,c_48205]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_342,plain,
% 58.83/8.00      ( ~ v1_funct_2(X0,X1,X2)
% 58.83/8.00      | v1_funct_2(X3,X4,X5)
% 58.83/8.00      | X3 != X0
% 58.83/8.00      | X4 != X1
% 58.83/8.00      | X5 != X2 ),
% 58.83/8.00      theory(equality) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_1389,plain,
% 58.83/8.00      ( v1_funct_2(X0,X1,X2)
% 58.83/8.00      | ~ v1_funct_2(sK3,sK0,sK1)
% 58.83/8.00      | X0 != sK3
% 58.83/8.00      | X2 != sK1
% 58.83/8.00      | X1 != sK0 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_342]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_66535,plain,
% 58.83/8.00      ( v1_funct_2(X0,X1,sK1)
% 58.83/8.00      | ~ v1_funct_2(sK3,sK0,sK1)
% 58.83/8.00      | X0 != sK3
% 58.83/8.00      | X1 != sK0
% 58.83/8.00      | sK1 != sK1 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_1389]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_66537,plain,
% 58.83/8.00      ( ~ v1_funct_2(sK3,sK0,sK1)
% 58.83/8.00      | v1_funct_2(k1_xboole_0,k1_xboole_0,sK1)
% 58.83/8.00      | sK1 != sK1
% 58.83/8.00      | k1_xboole_0 != sK3
% 58.83/8.00      | k1_xboole_0 != sK0 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_66535]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_3021,plain,
% 58.83/8.00      ( X0 != X1
% 58.83/8.00      | k2_partfun1(sK0,sK1,sK3,X2) != X1
% 58.83/8.00      | k2_partfun1(sK0,sK1,sK3,X2) = X0 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_334]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_10512,plain,
% 58.83/8.00      ( X0 != k2_partfun1(sK0,sK1,sK3,X1)
% 58.83/8.00      | k2_partfun1(sK0,sK1,sK3,X2) = X0
% 58.83/8.00      | k2_partfun1(sK0,sK1,sK3,X2) != k2_partfun1(sK0,sK1,sK3,X1) ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_3021]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_81575,plain,
% 58.83/8.00      ( X0 != k2_partfun1(sK0,sK1,sK3,X1)
% 58.83/8.00      | k2_partfun1(sK0,sK1,sK3,sK2) = X0
% 58.83/8.00      | k2_partfun1(sK0,sK1,sK3,sK2) != k2_partfun1(sK0,sK1,sK3,X1) ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_10512]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_81576,plain,
% 58.83/8.00      ( k2_partfun1(sK0,sK1,sK3,sK2) != k2_partfun1(sK0,sK1,sK3,k1_xboole_0)
% 58.83/8.00      | k2_partfun1(sK0,sK1,sK3,sK2) = k1_xboole_0
% 58.83/8.00      | k1_xboole_0 != k2_partfun1(sK0,sK1,sK3,k1_xboole_0) ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_81575]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_96507,plain,
% 58.83/8.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 58.83/8.00      | r1_tarski(X0,k2_zfmisc_1(sK2,sK1)) ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_6]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_96509,plain,
% 58.83/8.00      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 58.83/8.00      | r1_tarski(k1_xboole_0,k2_zfmisc_1(sK2,sK1)) ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_96507]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_97286,plain,
% 58.83/8.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_4]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_100857,plain,
% 58.83/8.00      ( ~ v1_funct_2(X0,X1,X2)
% 58.83/8.00      | v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
% 58.83/8.00      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 58.83/8.00      | sK2 != X1
% 58.83/8.00      | sK1 != X2 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_342]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_105036,plain,
% 58.83/8.00      ( ~ v1_funct_2(X0,X1,sK1)
% 58.83/8.00      | v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
% 58.83/8.00      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 58.83/8.00      | sK2 != X1
% 58.83/8.00      | sK1 != sK1 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_100857]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_105038,plain,
% 58.83/8.00      ( v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
% 58.83/8.00      | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK1)
% 58.83/8.00      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 58.83/8.00      | sK2 != k1_xboole_0
% 58.83/8.00      | sK1 != sK1 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_105036]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_98490,plain,
% 58.83/8.00      ( ~ r1_tarski(X0,X1)
% 58.83/8.00      | r1_tarski(sK2,k1_xboole_0)
% 58.83/8.00      | sK2 != X0
% 58.83/8.00      | k1_xboole_0 != X1 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_335]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_104103,plain,
% 58.83/8.00      ( ~ r1_tarski(sK2,X0)
% 58.83/8.00      | r1_tarski(sK2,k1_xboole_0)
% 58.83/8.00      | sK2 != sK2
% 58.83/8.00      | k1_xboole_0 != X0 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_98490]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_105825,plain,
% 58.83/8.00      ( ~ r1_tarski(sK2,sK0)
% 58.83/8.00      | r1_tarski(sK2,k1_xboole_0)
% 58.83/8.00      | sK2 != sK2
% 58.83/8.00      | k1_xboole_0 != sK0 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_104103]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_110385,plain,
% 58.83/8.00      ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),k2_relat_1(X0))) = k2_relat_1(X0)
% 58.83/8.00      | v5_relat_1(X0,k1_relat_1(k7_relat_1(sK3,sK2))) != iProver_top
% 58.83/8.00      | v1_relat_1(X0) != iProver_top
% 58.83/8.00      | v1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2)) != iProver_top ),
% 58.83/8.00      inference(global_propositional_subsumption,
% 58.83/8.00                [status(thm)],
% 58.83/8.00                [c_12938,c_31,c_30,c_29,c_28,c_27,c_103,c_104,c_1306,
% 58.83/8.00                 c_1375,c_1456,c_1474,c_1485,c_1770,c_1768,c_1799,c_1855,
% 58.83/8.00                 c_2419,c_2828,c_3027,c_4217,c_4681,c_5861,c_5882,c_6046,
% 58.83/8.00                 c_14498,c_20674,c_21017,c_25845,c_25846,c_48211,c_49744,
% 58.83/8.00                 c_66537,c_81576,c_96509,c_97286,c_105038,c_105825]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_7155,plain,
% 58.83/8.00      ( k2_partfun1(sK0,sK1,k7_relat_1(sK3,X0),X1) = k7_relat_1(k7_relat_1(sK3,X0),X1)
% 58.83/8.00      | v1_funct_1(k7_relat_1(sK3,X0)) != iProver_top ),
% 58.83/8.00      inference(superposition,[status(thm)],[c_7147,c_977]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_6827,plain,
% 58.83/8.00      ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 58.83/8.00      inference(demodulation,[status(thm)],[c_6820,c_1542]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_9176,plain,
% 58.83/8.00      ( k2_partfun1(sK0,sK1,k7_relat_1(sK3,X0),X1) = k7_relat_1(k7_relat_1(sK3,X0),X1) ),
% 58.83/8.00      inference(global_propositional_subsumption,
% 58.83/8.00                [status(thm)],
% 58.83/8.00                [c_7155,c_6827]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_1945,plain,
% 58.83/8.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 58.83/8.00      | r1_tarski(k2_partfun1(X1,X2,X0,X3),k2_zfmisc_1(X1,X2)) = iProver_top
% 58.83/8.00      | v1_funct_1(X0) != iProver_top ),
% 58.83/8.00      inference(superposition,[status(thm)],[c_979,c_996]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_9428,plain,
% 58.83/8.00      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 58.83/8.00      | r1_tarski(k7_relat_1(k7_relat_1(sK3,X0),X1),k2_zfmisc_1(sK0,sK1)) = iProver_top
% 58.83/8.00      | v1_funct_1(k7_relat_1(sK3,X0)) != iProver_top ),
% 58.83/8.00      inference(superposition,[status(thm)],[c_9176,c_1945]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_10766,plain,
% 58.83/8.00      ( r1_tarski(k7_relat_1(k7_relat_1(sK3,X0),X1),k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 58.83/8.00      inference(global_propositional_subsumption,
% 58.83/8.00                [status(thm)],
% 58.83/8.00                [c_9428,c_32,c_34,c_6827,c_6854]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_2136,plain,
% 58.83/8.00      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 58.83/8.00      | v1_relat_1(X0) = iProver_top ),
% 58.83/8.00      inference(superposition,[status(thm)],[c_997,c_989]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_10773,plain,
% 58.83/8.00      ( v1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),X1)) = iProver_top ),
% 58.83/8.00      inference(superposition,[status(thm)],[c_10766,c_2136]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_110395,plain,
% 58.83/8.00      ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),k2_relat_1(X0))) = k2_relat_1(X0)
% 58.83/8.00      | v5_relat_1(X0,k1_relat_1(k7_relat_1(sK3,sK2))) != iProver_top
% 58.83/8.00      | v1_relat_1(X0) != iProver_top ),
% 58.83/8.00      inference(forward_subsumption_resolution,
% 58.83/8.00                [status(thm)],
% 58.83/8.00                [c_110385,c_10773]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_110409,plain,
% 58.83/8.00      ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),k2_relat_1(X0))) = k2_relat_1(X0)
% 58.83/8.00      | sK1 = k1_xboole_0
% 58.83/8.00      | v5_relat_1(X0,sK2) != iProver_top
% 58.83/8.00      | v1_relat_1(X0) != iProver_top ),
% 58.83/8.00      inference(superposition,[status(thm)],[c_4715,c_110395]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_110950,plain,
% 58.83/8.00      ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),k2_relat_1(X0))) = k2_relat_1(X0)
% 58.83/8.00      | v5_relat_1(X0,sK2) != iProver_top
% 58.83/8.00      | v1_relat_1(X0) != iProver_top ),
% 58.83/8.00      inference(global_propositional_subsumption,
% 58.83/8.00                [status(thm)],
% 58.83/8.00                [c_110409,c_31,c_30,c_29,c_28,c_27,c_103,c_104,c_1306,
% 58.83/8.00                 c_1375,c_1456,c_1474,c_1485,c_1770,c_1768,c_1799,c_1855,
% 58.83/8.00                 c_2419,c_2828,c_3027,c_4217,c_4681,c_5861,c_5882,c_6046,
% 58.83/8.00                 c_14498,c_20674,c_21017,c_25845,c_25846,c_48211,c_49744,
% 58.83/8.00                 c_66537,c_81576,c_96509,c_97286,c_105038,c_105825]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_110962,plain,
% 58.83/8.00      ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),k2_relat_1(k2_partfun1(X0,sK2,X1,X2)))) = k2_relat_1(k2_partfun1(X0,sK2,X1,X2))
% 58.83/8.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 58.83/8.00      | v1_funct_1(X1) != iProver_top
% 58.83/8.00      | v1_relat_1(k2_partfun1(X0,sK2,X1,X2)) != iProver_top ),
% 58.83/8.00      inference(superposition,[status(thm)],[c_2930,c_110950]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_2137,plain,
% 58.83/8.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 58.83/8.00      | v1_funct_1(X0) != iProver_top
% 58.83/8.00      | v1_relat_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
% 58.83/8.00      inference(superposition,[status(thm)],[c_979,c_989]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_111476,plain,
% 58.83/8.00      ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),k2_relat_1(k2_partfun1(X0,sK2,X1,X2)))) = k2_relat_1(k2_partfun1(X0,sK2,X1,X2))
% 58.83/8.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 58.83/8.00      | v1_funct_1(X1) != iProver_top ),
% 58.83/8.00      inference(forward_subsumption_resolution,
% 58.83/8.00                [status(thm)],
% 58.83/8.00                [c_110962,c_2137]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_111484,plain,
% 58.83/8.00      ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),k2_relat_1(k2_partfun1(k1_xboole_0,sK2,X0,X1)))) = k2_relat_1(k2_partfun1(k1_xboole_0,sK2,X0,X1))
% 58.83/8.00      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 58.83/8.00      | v1_funct_1(X0) != iProver_top ),
% 58.83/8.00      inference(superposition,[status(thm)],[c_2,c_111476]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_111915,plain,
% 58.83/8.00      ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),k2_relat_1(k2_partfun1(k1_xboole_0,sK2,sK3,X0)))) = k2_relat_1(k2_partfun1(k1_xboole_0,sK2,sK3,X0))
% 58.83/8.00      | r1_tarski(sK0,k1_xboole_0) != iProver_top
% 58.83/8.00      | v1_funct_1(sK3) != iProver_top ),
% 58.83/8.00      inference(superposition,[status(thm)],[c_58565,c_111484]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_1459,plain,
% 58.83/8.00      ( k1_xboole_0 = sK3 | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
% 58.83/8.00      inference(predicate_to_equality,[status(thm)],[c_1456]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_2693,plain,
% 58.83/8.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 58.83/8.00      | ~ v1_funct_1(sK3)
% 58.83/8.00      | k2_partfun1(sK0,sK1,sK3,sK2) = k7_relat_1(sK3,sK2) ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_1472]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_5862,plain,
% 58.83/8.00      ( k2_partfun1(sK0,sK1,sK3,sK2) != k2_partfun1(sK0,sK1,sK3,sK2)
% 58.83/8.00      | k2_partfun1(sK0,sK1,sK3,sK2) = k1_xboole_0
% 58.83/8.00      | k1_xboole_0 != k2_partfun1(sK0,sK1,sK3,sK2) ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_5860]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_59364,plain,
% 58.83/8.00      ( r1_tarski(sK3,k1_xboole_0) = iProver_top
% 58.83/8.00      | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 58.83/8.00      inference(superposition,[status(thm)],[c_58565,c_996]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_2724,plain,
% 58.83/8.00      ( ~ r1_tarski(X0,X1)
% 58.83/8.00      | r1_tarski(k2_partfun1(sK0,sK1,sK3,X2),k1_xboole_0)
% 58.83/8.00      | k2_partfun1(sK0,sK1,sK3,X2) != X0
% 58.83/8.00      | k1_xboole_0 != X1 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_335]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_6024,plain,
% 58.83/8.00      ( r1_tarski(k2_partfun1(sK0,sK1,sK3,X0),k1_xboole_0)
% 58.83/8.00      | ~ r1_tarski(k7_relat_1(sK3,X0),X1)
% 58.83/8.00      | k2_partfun1(sK0,sK1,sK3,X0) != k7_relat_1(sK3,X0)
% 58.83/8.00      | k1_xboole_0 != X1 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_2724]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_9085,plain,
% 58.83/8.00      ( r1_tarski(k2_partfun1(sK0,sK1,sK3,X0),k1_xboole_0)
% 58.83/8.00      | ~ r1_tarski(k7_relat_1(sK3,X0),sK3)
% 58.83/8.00      | k2_partfun1(sK0,sK1,sK3,X0) != k7_relat_1(sK3,X0)
% 58.83/8.00      | k1_xboole_0 != sK3 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_6024]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_70674,plain,
% 58.83/8.00      ( r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k1_xboole_0)
% 58.83/8.00      | ~ r1_tarski(k7_relat_1(sK3,sK2),sK3)
% 58.83/8.00      | k2_partfun1(sK0,sK1,sK3,sK2) != k7_relat_1(sK3,sK2)
% 58.83/8.00      | k1_xboole_0 != sK3 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_9085]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_2328,plain,
% 58.83/8.00      ( ~ r1_tarski(k2_partfun1(sK0,sK1,sK3,X0),k1_xboole_0)
% 58.83/8.00      | k1_xboole_0 = k2_partfun1(sK0,sK1,sK3,X0) ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_0]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_70689,plain,
% 58.83/8.00      ( ~ r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k1_xboole_0)
% 58.83/8.00      | k1_xboole_0 = k2_partfun1(sK0,sK1,sK3,sK2) ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_2328]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_11,plain,
% 58.83/8.00      ( r1_tarski(k7_relat_1(X0,X1),X0) | ~ v1_relat_1(X0) ),
% 58.83/8.00      inference(cnf_transformation,[],[f60]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_105775,plain,
% 58.83/8.00      ( r1_tarski(k7_relat_1(sK3,sK2),sK3) | ~ v1_relat_1(sK3) ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_11]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_106222,plain,
% 58.83/8.00      ( ~ r1_tarski(sK0,k1_xboole_0) | k1_xboole_0 = sK0 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_0]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_106223,plain,
% 58.83/8.00      ( k1_xboole_0 = sK0 | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 58.83/8.00      inference(predicate_to_equality,[status(thm)],[c_106222]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_112910,plain,
% 58.83/8.00      ( r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 58.83/8.00      inference(global_propositional_subsumption,
% 58.83/8.00                [status(thm)],
% 58.83/8.00                [c_111915,c_31,c_30,c_29,c_28,c_1275,c_1459,c_1770,
% 58.83/8.00                 c_1768,c_1799,c_2419,c_2693,c_2828,c_5862,c_5861,c_5882,
% 58.83/8.00                 c_14498,c_59364,c_66537,c_70674,c_70689,c_96509,c_97286,
% 58.83/8.00                 c_105038,c_105775,c_105825,c_106223]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_112912,plain,
% 58.83/8.00      ( ~ r1_tarski(sK0,k1_xboole_0) ),
% 58.83/8.00      inference(predicate_to_equality_rev,[status(thm)],[c_112910]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_95751,plain,
% 58.83/8.00      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_334]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_96570,plain,
% 58.83/8.00      ( X0 != sK2 | sK2 = X0 | sK2 != sK2 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_95751]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_97546,plain,
% 58.83/8.00      ( k1_relat_1(k7_relat_1(X0,sK2)) != sK2
% 58.83/8.00      | sK2 = k1_relat_1(k7_relat_1(X0,sK2))
% 58.83/8.00      | sK2 != sK2 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_96570]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_108505,plain,
% 58.83/8.00      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 58.83/8.00      | sK2 = k1_relat_1(k7_relat_1(sK3,sK2))
% 58.83/8.00      | sK2 != sK2 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_97546]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_95552,plain,
% 58.83/8.00      ( ~ r1_tarski(X0,X1)
% 58.83/8.00      | r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2)
% 58.83/8.00      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != X0
% 58.83/8.00      | sK2 != X1 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_335]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_95747,plain,
% 58.83/8.00      ( ~ r1_tarski(X0,sK2)
% 58.83/8.00      | r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2)
% 58.83/8.00      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != X0
% 58.83/8.00      | sK2 != sK2 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_95552]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_96549,plain,
% 58.83/8.00      ( ~ r1_tarski(k1_relat_1(X0),sK2)
% 58.83/8.00      | r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2)
% 58.83/8.00      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != k1_relat_1(X0)
% 58.83/8.00      | sK2 != sK2 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_95747]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_100165,plain,
% 58.83/8.00      ( r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2)
% 58.83/8.00      | ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
% 58.83/8.00      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != k1_relat_1(k7_relat_1(sK3,sK2))
% 58.83/8.00      | sK2 != sK2 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_96549]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_340,plain,
% 58.83/8.00      ( X0 != X1 | k1_relat_1(X0) = k1_relat_1(X1) ),
% 58.83/8.00      theory(equality) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_96550,plain,
% 58.83/8.00      ( k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 58.83/8.00      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) = k1_relat_1(X0) ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_340]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_97967,plain,
% 58.83/8.00      ( k2_partfun1(sK0,sK1,sK3,sK2) != k7_relat_1(sK3,sK2)
% 58.83/8.00      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2)) ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_96550]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_49274,plain,
% 58.83/8.00      ( v1_relat_1(k7_relat_1(sK3,sK2)) | ~ v1_relat_1(sK3) ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_9]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_5192,plain,
% 58.83/8.00      ( ~ v5_relat_1(X0,sK1)
% 58.83/8.00      | r1_tarski(k2_relat_1(X0),sK1)
% 58.83/8.00      | ~ v1_relat_1(X0) ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_8]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_24212,plain,
% 58.83/8.00      ( ~ v5_relat_1(k2_partfun1(sK0,sK1,sK3,sK2),sK1)
% 58.83/8.00      | r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
% 58.83/8.00      | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_5192]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_6048,plain,
% 58.83/8.00      ( X0 != X1 | sK0 != X1 | sK0 = X0 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_334]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_14842,plain,
% 58.83/8.00      ( X0 != sK0 | sK0 = X0 | sK0 != sK0 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_6048]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_14843,plain,
% 58.83/8.00      ( sK0 != sK0 | sK0 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_14842]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_12045,plain,
% 58.83/8.00      ( sK1 = k1_xboole_0
% 58.83/8.00      | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) = iProver_top
% 58.83/8.00      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 58.83/8.00      inference(superposition,[status(thm)],[c_11806,c_992]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_12073,plain,
% 58.83/8.00      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
% 58.83/8.00      | ~ v1_relat_1(k7_relat_1(sK3,sK2))
% 58.83/8.00      | sK1 = k1_xboole_0 ),
% 58.83/8.00      inference(predicate_to_equality_rev,[status(thm)],[c_12045]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_1346,plain,
% 58.83/8.00      ( m1_subset_1(k2_partfun1(X0,X1,sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 58.83/8.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 58.83/8.00      | ~ v1_funct_1(sK3) ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_23]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_1531,plain,
% 58.83/8.00      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 58.83/8.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 58.83/8.00      | ~ v1_funct_1(sK3) ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_1346]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_8654,plain,
% 58.83/8.00      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 58.83/8.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 58.83/8.00      | ~ v1_funct_1(sK3) ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_1531]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_4003,plain,
% 58.83/8.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 58.83/8.00      | v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_13]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_8653,plain,
% 58.83/8.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 58.83/8.00      | v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_4003]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_5256,plain,
% 58.83/8.00      ( v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) != iProver_top
% 58.83/8.00      | r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2) != iProver_top
% 58.83/8.00      | r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1) != iProver_top
% 58.83/8.00      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top
% 58.83/8.00      | v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 58.83/8.00      inference(superposition,[status(thm)],[c_986,c_976]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_3385,plain,
% 58.83/8.00      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 58.83/8.00      | ~ r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2)
% 58.83/8.00      | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
% 58.83/8.00      | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_16]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_3386,plain,
% 58.83/8.00      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top
% 58.83/8.00      | r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2) != iProver_top
% 58.83/8.00      | r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1) != iProver_top
% 58.83/8.00      | v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 58.83/8.00      inference(predicate_to_equality,[status(thm)],[c_3385]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_4319,plain,
% 58.83/8.00      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) | ~ v1_funct_1(sK3) ),
% 58.83/8.00      inference(resolution,[status(thm)],[c_24,c_29]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_1425,plain,
% 58.83/8.00      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) | ~ v1_funct_1(sK3) ),
% 58.83/8.00      inference(predicate_to_equality_rev,[status(thm)],[c_1406]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_4773,plain,
% 58.83/8.00      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) ),
% 58.83/8.00      inference(global_propositional_subsumption,
% 58.83/8.00                [status(thm)],
% 58.83/8.00                [c_4319,c_31,c_1425]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_4784,plain,
% 58.83/8.00      ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
% 58.83/8.00      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 58.83/8.00      inference(backward_subsumption_resolution,
% 58.83/8.00                [status(thm)],
% 58.83/8.00                [c_4773,c_26]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_4785,plain,
% 58.83/8.00      ( v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) != iProver_top
% 58.83/8.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 58.83/8.00      inference(predicate_to_equality,[status(thm)],[c_4784]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_5741,plain,
% 58.83/8.00      ( r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1) != iProver_top
% 58.83/8.00      | r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2) != iProver_top
% 58.83/8.00      | v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) != iProver_top
% 58.83/8.00      | v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 58.83/8.00      inference(global_propositional_subsumption,
% 58.83/8.00                [status(thm)],
% 58.83/8.00                [c_5256,c_3386,c_4785]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_5742,plain,
% 58.83/8.00      ( v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) != iProver_top
% 58.83/8.00      | r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2) != iProver_top
% 58.83/8.00      | r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1) != iProver_top
% 58.83/8.00      | v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 58.83/8.00      inference(renaming,[status(thm)],[c_5741]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_5743,plain,
% 58.83/8.00      ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
% 58.83/8.00      | ~ r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2)
% 58.83/8.00      | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
% 58.83/8.00      | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 58.83/8.00      inference(predicate_to_equality_rev,[status(thm)],[c_5742]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_101,plain,
% 58.83/8.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_4]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(c_95,plain,
% 58.83/8.00      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 58.83/8.00      | r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 58.83/8.00      inference(instantiation,[status(thm)],[c_6]) ).
% 58.83/8.00  
% 58.83/8.00  cnf(contradiction,plain,
% 58.83/8.00      ( $false ),
% 58.83/8.00      inference(minisat,
% 58.83/8.00                [status(thm)],
% 58.83/8.00                [c_205314,c_165443,c_156776,c_136856,c_124362,c_114583,
% 58.83/8.00                 c_112912,c_108505,c_100165,c_97967,c_49274,c_24212,
% 58.83/8.00                 c_14843,c_12073,c_8654,c_8653,c_6046,c_5743,c_4715,
% 58.83/8.00                 c_3385,c_2828,c_2693,c_1306,c_1275,c_104,c_103,c_101,
% 58.83/8.00                 c_95,c_27,c_29,c_31]) ).
% 58.83/8.00  
% 58.83/8.00  
% 58.83/8.00  % SZS output end CNFRefutation for theBenchmark.p
% 58.83/8.00  
% 58.83/8.00  ------                               Statistics
% 58.83/8.00  
% 58.83/8.00  ------ Selected
% 58.83/8.00  
% 58.83/8.00  total_time:                             7.108
% 58.83/8.00  
%------------------------------------------------------------------------------
