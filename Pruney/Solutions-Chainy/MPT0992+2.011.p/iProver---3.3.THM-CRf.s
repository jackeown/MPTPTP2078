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
% DateTime   : Thu Dec  3 12:03:48 EST 2020

% Result     : Theorem 19.81s
% Output     : CNFRefutation 19.81s
% Verified   : 
% Statistics : Number of formulae       :  224 (14328 expanded)
%              Number of clauses        :  160 (5160 expanded)
%              Number of leaves         :   17 (2690 expanded)
%              Depth                    :   41
%              Number of atoms          :  592 (76450 expanded)
%              Number of equality atoms :  370 (22397 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f41,plain,
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

fof(f42,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f37,f41])).

fof(f67,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f42])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f65,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f28])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f68,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f12,axiom,(
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

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f66,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f70,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f42])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f69,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f42])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f38])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f72,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f71,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f46])).

fof(f1,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f43,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f76,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f59])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_635,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_638,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4966,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_635,c_638])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_962,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1114,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_962])).

cnf(c_5015,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4966,c_27,c_25,c_1114])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_640,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_5033,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5015,c_640])).

cnf(c_28,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_30,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_957,plain,
    ( m1_subset_1(k2_partfun1(X0,X1,sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1204,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_957])).

cnf(c_1205,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1204])).

cnf(c_227,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1773,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_227])).

cnf(c_228,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1791,plain,
    ( X0 != X1
    | X0 = k2_partfun1(sK0,sK1,sK3,X2)
    | k2_partfun1(sK0,sK1,sK3,X2) != X1 ),
    inference(instantiation,[status(thm)],[c_228])).

cnf(c_2467,plain,
    ( X0 = k2_partfun1(sK0,sK1,sK3,X1)
    | X0 != k7_relat_1(sK3,X1)
    | k2_partfun1(sK0,sK1,sK3,X1) != k7_relat_1(sK3,X1) ),
    inference(instantiation,[status(thm)],[c_1791])).

cnf(c_2886,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) != k7_relat_1(sK3,X0)
    | k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0)
    | k7_relat_1(sK3,X0) != k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_2467])).

cnf(c_2887,plain,
    ( k7_relat_1(sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_227])).

cnf(c_233,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1534,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,X2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | X0 != k2_partfun1(sK0,sK1,sK3,X2)
    | X1 != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_233])).

cnf(c_2123,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | X0 != k2_partfun1(sK0,sK1,sK3,X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_1534])).

cnf(c_4061,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k7_relat_1(sK3,X0) != k2_partfun1(sK0,sK1,sK3,X0)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_2123])).

cnf(c_4067,plain,
    ( k7_relat_1(sK3,X0) != k2_partfun1(sK0,sK1,sK3,X0)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4061])).

cnf(c_6809,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5033,c_27,c_28,c_25,c_30,c_1114,c_1205,c_1773,c_2886,c_2887,c_4067])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_647,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_6822,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6809,c_647])).

cnf(c_24,negated_conjecture,
    ( r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_636,plain,
    ( r1_tarski(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_641,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2372,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | sK1 = k1_xboole_0
    | v1_funct_2(sK3,sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_635,c_641])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_648,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1848,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_635,c_648])).

cnf(c_2386,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0
    | v1_funct_2(sK3,sK0,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2372,c_1848])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_29,plain,
    ( v1_funct_2(sK3,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2900,plain,
    ( sK1 = k1_xboole_0
    | k1_relat_1(sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2386,c_29])).

cnf(c_2901,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2900])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_651,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2904,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2901,c_651])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_891,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_892,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_891])).

cnf(c_3062,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | sK1 = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2904,c_30,c_892])).

cnf(c_3063,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3062])).

cnf(c_3070,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_636,c_3063])).

cnf(c_650,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1370,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_635,c_650])).

cnf(c_7,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_652,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_10,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_649,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_8304,plain,
    ( v4_relat_1(k7_relat_1(sK3,X0),X1) = iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6822,c_649])).

cnf(c_10186,plain,
    ( v4_relat_1(k7_relat_1(sK3,X0),X0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_652,c_8304])).

cnf(c_11401,plain,
    ( v4_relat_1(k7_relat_1(sK3,X0),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10186,c_30,c_892])).

cnf(c_6,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_653,plain,
    ( k7_relat_1(X0,X1) = X0
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_11408,plain,
    ( k7_relat_1(k7_relat_1(sK3,X0),X0) = k7_relat_1(sK3,X0)
    | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11401,c_653])).

cnf(c_1657,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_640,c_650])).

cnf(c_6096,plain,
    ( v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_635,c_1657])).

cnf(c_6108,plain,
    ( v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6096,c_5015])).

cnf(c_11588,plain,
    ( k7_relat_1(k7_relat_1(sK3,X0),X0) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11408,c_28,c_6108])).

cnf(c_11592,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X0) = iProver_top
    | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11588,c_652])).

cnf(c_998,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X0)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_999,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_998])).

cnf(c_11603,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11592,c_30,c_892,c_999])).

cnf(c_11618,plain,
    ( k1_relat_1(k7_relat_1(X0,k1_relat_1(k7_relat_1(sK3,k1_relat_1(X0))))) = k1_relat_1(k7_relat_1(sK3,k1_relat_1(X0)))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11603,c_651])).

cnf(c_12650,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3))))) = k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3))) ),
    inference(superposition,[status(thm)],[c_1370,c_11618])).

cnf(c_12673,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))),X0)) = X0
    | r1_tarski(X0,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_12650,c_651])).

cnf(c_6441,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6108,c_28])).

cnf(c_14791,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))),X0)) = X0
    | r1_tarski(X0,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_12673,c_6441])).

cnf(c_14801,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))),X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,k1_relat_1(k7_relat_1(sK3,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2901,c_14791])).

cnf(c_1701,plain,
    ( v4_relat_1(sK3,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_635,c_649])).

cnf(c_2285,plain,
    ( k7_relat_1(sK3,sK0) = sK3
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1701,c_653])).

cnf(c_918,plain,
    ( v4_relat_1(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1012,plain,
    ( ~ v4_relat_1(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | k7_relat_1(sK3,sK0) = sK3 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2685,plain,
    ( k7_relat_1(sK3,sK0) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2285,c_25,c_891,c_918,c_1012])).

cnf(c_14805,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))),X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14801,c_2685])).

cnf(c_15956,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))),X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2901,c_14805])).

cnf(c_16219,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))),sK2)) = sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_636,c_15956])).

cnf(c_2516,plain,
    ( k1_relat_1(k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))) = k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_652,c_651])).

cnf(c_30318,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),k1_relat_1(k7_relat_1(X1,k1_relat_1(k7_relat_1(sK3,X0)))))) = k1_relat_1(k7_relat_1(X1,k1_relat_1(k7_relat_1(sK3,X0))))
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6441,c_2516])).

cnf(c_31051,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),k1_relat_1(k7_relat_1(k7_relat_1(sK3,X1),k1_relat_1(k7_relat_1(sK3,X0)))))) = k1_relat_1(k7_relat_1(k7_relat_1(sK3,X1),k1_relat_1(k7_relat_1(sK3,X0)))) ),
    inference(superposition,[status(thm)],[c_6441,c_30318])).

cnf(c_31509,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),sK2)))) = k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),k1_relat_1(k7_relat_1(sK3,sK2))))
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3070,c_31051])).

cnf(c_3096,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK2) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3070,c_651])).

cnf(c_6452,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6441,c_3096])).

cnf(c_10967,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),k1_relat_1(k7_relat_1(X0,sK2)))) = k1_relat_1(k7_relat_1(X0,sK2))
    | sK1 = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_652,c_6452])).

cnf(c_20315,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),sK2)))) = k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),sK2))
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6441,c_10967])).

cnf(c_31656,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),k1_relat_1(k7_relat_1(sK3,sK2)))) = k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),sK2))
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_31509,c_20315])).

cnf(c_33809,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),sK2)),k1_relat_1(k7_relat_1(sK3,sK2))) = iProver_top
    | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_31656,c_652])).

cnf(c_37280,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),sK2)),k1_relat_1(k7_relat_1(sK3,sK2))) = iProver_top
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_33809,c_28,c_6108])).

cnf(c_37281,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),sK2)),k1_relat_1(k7_relat_1(sK3,sK2))) = iProver_top ),
    inference(renaming,[status(thm)],[c_37280])).

cnf(c_37291,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK2,k1_relat_1(k7_relat_1(sK3,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_16219,c_37281])).

cnf(c_8301,plain,
    ( k1_relset_1(X0,sK1,k7_relat_1(sK3,X1)) = k1_relat_1(k7_relat_1(sK3,X1))
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,X1)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6822,c_648])).

cnf(c_13857,plain,
    ( k1_relset_1(X0,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
    | sK1 = k1_xboole_0
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3070,c_8301])).

cnf(c_37560,plain,
    ( k1_relset_1(k1_relat_1(k7_relat_1(sK3,sK2)),sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_37291,c_13857])).

cnf(c_16,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_643,plain,
    ( k1_relset_1(X0,X1,X2) != X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_39295,plain,
    ( sK1 = k1_xboole_0
    | v1_funct_2(k7_relat_1(sK3,sK2),k1_relat_1(k7_relat_1(sK3,sK2)),sK1) = iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,sK2)),sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_37560,c_643])).

cnf(c_72970,plain,
    ( sK1 = k1_xboole_0
    | v1_funct_2(k7_relat_1(sK3,sK2),k1_relat_1(k7_relat_1(sK3,sK2)),sK1) = iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3070,c_39295])).

cnf(c_22,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_637,plain,
    ( v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_5019,plain,
    ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5015,c_637])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_639,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1041,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_635,c_639])).

cnf(c_1300,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1041,c_28])).

cnf(c_5020,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5015,c_1300])).

cnf(c_5026,plain,
    ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5019,c_5020])).

cnf(c_3095,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK2,sK2) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3070,c_652])).

cnf(c_3257,plain,
    ( r1_tarski(sK2,sK2) = iProver_top
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3095,c_30,c_892])).

cnf(c_3258,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK2,sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_3257])).

cnf(c_14129,plain,
    ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3258,c_13857])).

cnf(c_15053,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | sK1 = k1_xboole_0
    | v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) = iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_14129,c_643])).

cnf(c_73604,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_72970,c_3070,c_5026,c_15053])).

cnf(c_73611,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6822,c_73604])).

cnf(c_73820,plain,
    ( sK1 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_73611,c_11603])).

cnf(c_73933,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_73820,c_6809])).

cnf(c_23,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_73947,plain,
    ( sK0 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_73820,c_23])).

cnf(c_73948,plain,
    ( sK0 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_73947])).

cnf(c_73988,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_73933,c_73948])).

cnf(c_2,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_73990,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_73988,c_2])).

cnf(c_73937,plain,
    ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,k1_xboole_0) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_73820,c_5026])).

cnf(c_1,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_73973,plain,
    ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,k1_xboole_0) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_73937,c_1])).

cnf(c_73992,plain,
    ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,k1_xboole_0) != iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_73990,c_73973])).

cnf(c_74158,plain,
    ( k7_relat_1(sK3,k1_xboole_0) = sK3 ),
    inference(demodulation,[status(thm)],[c_73948,c_2685])).

cnf(c_74160,plain,
    ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_73948,c_636])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_656,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_74532,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_74160,c_656])).

cnf(c_82138,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_73992,c_74158,c_74532])).

cnf(c_8297,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_6822])).

cnf(c_8687,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_652,c_8297])).

cnf(c_1001,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,k1_xboole_0)),k1_xboole_0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_999])).

cnf(c_8354,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,k1_xboole_0)),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8297])).

cnf(c_8738,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8687,c_30,c_892,c_1001,c_8354])).

cnf(c_1850,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_648])).

cnf(c_8746,plain,
    ( k1_relset_1(k1_xboole_0,X0,k7_relat_1(sK3,k1_xboole_0)) = k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_8738,c_1850])).

cnf(c_1466,plain,
    ( k1_relat_1(k7_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_652,c_656])).

cnf(c_1570,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1370,c_1466])).

cnf(c_8757,plain,
    ( k1_relset_1(k1_xboole_0,X0,k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_8746,c_1570])).

cnf(c_15,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_644,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_739,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_644,c_2])).

cnf(c_9242,plain,
    ( v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,X0) = iProver_top
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8757,c_739])).

cnf(c_12532,plain,
    ( v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9242,c_30,c_892,c_1001,c_8354])).

cnf(c_75166,plain,
    ( v1_funct_2(sK3,k1_xboole_0,X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_74158,c_12532])).

cnf(c_82140,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_82138,c_75166])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:51:22 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 19.81/2.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.81/2.99  
% 19.81/2.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.81/2.99  
% 19.81/2.99  ------  iProver source info
% 19.81/2.99  
% 19.81/2.99  git: date: 2020-06-30 10:37:57 +0100
% 19.81/2.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.81/2.99  git: non_committed_changes: false
% 19.81/2.99  git: last_make_outside_of_git: false
% 19.81/2.99  
% 19.81/2.99  ------ 
% 19.81/2.99  ------ Parsing...
% 19.81/2.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.81/2.99  
% 19.81/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 19.81/2.99  
% 19.81/2.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.81/2.99  
% 19.81/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.81/2.99  ------ Proving...
% 19.81/2.99  ------ Problem Properties 
% 19.81/2.99  
% 19.81/2.99  
% 19.81/2.99  clauses                                 28
% 19.81/2.99  conjectures                             6
% 19.81/2.99  EPR                                     5
% 19.81/2.99  Horn                                    23
% 19.81/2.99  unary                                   7
% 19.81/2.99  binary                                  6
% 19.81/2.99  lits                                    67
% 19.81/2.99  lits eq                                 21
% 19.81/2.99  fd_pure                                 0
% 19.81/2.99  fd_pseudo                               0
% 19.81/2.99  fd_cond                                 5
% 19.81/2.99  fd_pseudo_cond                          0
% 19.81/2.99  AC symbols                              0
% 19.81/2.99  
% 19.81/2.99  ------ Input Options Time Limit: Unbounded
% 19.81/2.99  
% 19.81/2.99  
% 19.81/2.99  ------ 
% 19.81/2.99  Current options:
% 19.81/2.99  ------ 
% 19.81/2.99  
% 19.81/2.99  
% 19.81/2.99  
% 19.81/2.99  
% 19.81/2.99  ------ Proving...
% 19.81/2.99  
% 19.81/2.99  
% 19.81/2.99  % SZS status Theorem for theBenchmark.p
% 19.81/2.99  
% 19.81/2.99   Resolution empty clause
% 19.81/2.99  
% 19.81/2.99  % SZS output start CNFRefutation for theBenchmark.p
% 19.81/2.99  
% 19.81/2.99  fof(f15,conjecture,(
% 19.81/2.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 19.81/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.81/2.99  
% 19.81/2.99  fof(f16,negated_conjecture,(
% 19.81/2.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 19.81/2.99    inference(negated_conjecture,[],[f15])).
% 19.81/2.99  
% 19.81/2.99  fof(f36,plain,(
% 19.81/2.99    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 19.81/2.99    inference(ennf_transformation,[],[f16])).
% 19.81/2.99  
% 19.81/2.99  fof(f37,plain,(
% 19.81/2.99    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 19.81/2.99    inference(flattening,[],[f36])).
% 19.81/2.99  
% 19.81/2.99  fof(f41,plain,(
% 19.81/2.99    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 19.81/2.99    introduced(choice_axiom,[])).
% 19.81/2.99  
% 19.81/2.99  fof(f42,plain,(
% 19.81/2.99    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 19.81/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f37,f41])).
% 19.81/2.99  
% 19.81/2.99  fof(f67,plain,(
% 19.81/2.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 19.81/2.99    inference(cnf_transformation,[],[f42])).
% 19.81/2.99  
% 19.81/2.99  fof(f14,axiom,(
% 19.81/2.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 19.81/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.81/2.99  
% 19.81/2.99  fof(f34,plain,(
% 19.81/2.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 19.81/2.99    inference(ennf_transformation,[],[f14])).
% 19.81/2.99  
% 19.81/2.99  fof(f35,plain,(
% 19.81/2.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 19.81/2.99    inference(flattening,[],[f34])).
% 19.81/2.99  
% 19.81/2.99  fof(f64,plain,(
% 19.81/2.99    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 19.81/2.99    inference(cnf_transformation,[],[f35])).
% 19.81/2.99  
% 19.81/2.99  fof(f65,plain,(
% 19.81/2.99    v1_funct_1(sK3)),
% 19.81/2.99    inference(cnf_transformation,[],[f42])).
% 19.81/2.99  
% 19.81/2.99  fof(f13,axiom,(
% 19.81/2.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 19.81/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.81/2.99  
% 19.81/2.99  fof(f32,plain,(
% 19.81/2.99    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 19.81/2.99    inference(ennf_transformation,[],[f13])).
% 19.81/2.99  
% 19.81/2.99  fof(f33,plain,(
% 19.81/2.99    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 19.81/2.99    inference(flattening,[],[f32])).
% 19.81/2.99  
% 19.81/2.99  fof(f63,plain,(
% 19.81/2.99    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 19.81/2.99    inference(cnf_transformation,[],[f33])).
% 19.81/2.99  
% 19.81/2.99  fof(f11,axiom,(
% 19.81/2.99    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 19.81/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.81/2.99  
% 19.81/2.99  fof(f28,plain,(
% 19.81/2.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 19.81/2.99    inference(ennf_transformation,[],[f11])).
% 19.81/2.99  
% 19.81/2.99  fof(f29,plain,(
% 19.81/2.99    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 19.81/2.99    inference(flattening,[],[f28])).
% 19.81/2.99  
% 19.81/2.99  fof(f55,plain,(
% 19.81/2.99    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 19.81/2.99    inference(cnf_transformation,[],[f29])).
% 19.81/2.99  
% 19.81/2.99  fof(f68,plain,(
% 19.81/2.99    r1_tarski(sK2,sK0)),
% 19.81/2.99    inference(cnf_transformation,[],[f42])).
% 19.81/2.99  
% 19.81/2.99  fof(f12,axiom,(
% 19.81/2.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 19.81/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.81/2.99  
% 19.81/2.99  fof(f30,plain,(
% 19.81/2.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.81/2.99    inference(ennf_transformation,[],[f12])).
% 19.81/2.99  
% 19.81/2.99  fof(f31,plain,(
% 19.81/2.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.81/2.99    inference(flattening,[],[f30])).
% 19.81/2.99  
% 19.81/2.99  fof(f40,plain,(
% 19.81/2.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.81/2.99    inference(nnf_transformation,[],[f31])).
% 19.81/2.99  
% 19.81/2.99  fof(f56,plain,(
% 19.81/2.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 19.81/2.99    inference(cnf_transformation,[],[f40])).
% 19.81/2.99  
% 19.81/2.99  fof(f10,axiom,(
% 19.81/2.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 19.81/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.81/2.99  
% 19.81/2.99  fof(f27,plain,(
% 19.81/2.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.81/2.99    inference(ennf_transformation,[],[f10])).
% 19.81/2.99  
% 19.81/2.99  fof(f54,plain,(
% 19.81/2.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 19.81/2.99    inference(cnf_transformation,[],[f27])).
% 19.81/2.99  
% 19.81/2.99  fof(f66,plain,(
% 19.81/2.99    v1_funct_2(sK3,sK0,sK1)),
% 19.81/2.99    inference(cnf_transformation,[],[f42])).
% 19.81/2.99  
% 19.81/2.99  fof(f7,axiom,(
% 19.81/2.99    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 19.81/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.81/2.99  
% 19.81/2.99  fof(f23,plain,(
% 19.81/2.99    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 19.81/2.99    inference(ennf_transformation,[],[f7])).
% 19.81/2.99  
% 19.81/2.99  fof(f24,plain,(
% 19.81/2.99    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 19.81/2.99    inference(flattening,[],[f23])).
% 19.81/2.99  
% 19.81/2.99  fof(f51,plain,(
% 19.81/2.99    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 19.81/2.99    inference(cnf_transformation,[],[f24])).
% 19.81/2.99  
% 19.81/2.99  fof(f8,axiom,(
% 19.81/2.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 19.81/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.81/2.99  
% 19.81/2.99  fof(f25,plain,(
% 19.81/2.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.81/2.99    inference(ennf_transformation,[],[f8])).
% 19.81/2.99  
% 19.81/2.99  fof(f52,plain,(
% 19.81/2.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 19.81/2.99    inference(cnf_transformation,[],[f25])).
% 19.81/2.99  
% 19.81/2.99  fof(f6,axiom,(
% 19.81/2.99    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 19.81/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.81/2.99  
% 19.81/2.99  fof(f22,plain,(
% 19.81/2.99    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 19.81/2.99    inference(ennf_transformation,[],[f6])).
% 19.81/2.99  
% 19.81/2.99  fof(f50,plain,(
% 19.81/2.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 19.81/2.99    inference(cnf_transformation,[],[f22])).
% 19.81/2.99  
% 19.81/2.99  fof(f9,axiom,(
% 19.81/2.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 19.81/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.81/2.99  
% 19.81/2.99  fof(f17,plain,(
% 19.81/2.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 19.81/2.99    inference(pure_predicate_removal,[],[f9])).
% 19.81/2.99  
% 19.81/2.99  fof(f26,plain,(
% 19.81/2.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.81/2.99    inference(ennf_transformation,[],[f17])).
% 19.81/2.99  
% 19.81/2.99  fof(f53,plain,(
% 19.81/2.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 19.81/2.99    inference(cnf_transformation,[],[f26])).
% 19.81/2.99  
% 19.81/2.99  fof(f5,axiom,(
% 19.81/2.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 19.81/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.81/2.99  
% 19.81/2.99  fof(f20,plain,(
% 19.81/2.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 19.81/2.99    inference(ennf_transformation,[],[f5])).
% 19.81/2.99  
% 19.81/2.99  fof(f21,plain,(
% 19.81/2.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 19.81/2.99    inference(flattening,[],[f20])).
% 19.81/2.99  
% 19.81/2.99  fof(f49,plain,(
% 19.81/2.99    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 19.81/2.99    inference(cnf_transformation,[],[f21])).
% 19.81/2.99  
% 19.81/2.99  fof(f58,plain,(
% 19.81/2.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 19.81/2.99    inference(cnf_transformation,[],[f40])).
% 19.81/2.99  
% 19.81/2.99  fof(f70,plain,(
% 19.81/2.99    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 19.81/2.99    inference(cnf_transformation,[],[f42])).
% 19.81/2.99  
% 19.81/2.99  fof(f62,plain,(
% 19.81/2.99    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 19.81/2.99    inference(cnf_transformation,[],[f33])).
% 19.81/2.99  
% 19.81/2.99  fof(f69,plain,(
% 19.81/2.99    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 19.81/2.99    inference(cnf_transformation,[],[f42])).
% 19.81/2.99  
% 19.81/2.99  fof(f2,axiom,(
% 19.81/2.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 19.81/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.81/2.99  
% 19.81/2.99  fof(f38,plain,(
% 19.81/2.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 19.81/2.99    inference(nnf_transformation,[],[f2])).
% 19.81/2.99  
% 19.81/2.99  fof(f39,plain,(
% 19.81/2.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 19.81/2.99    inference(flattening,[],[f38])).
% 19.81/2.99  
% 19.81/2.99  fof(f45,plain,(
% 19.81/2.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 19.81/2.99    inference(cnf_transformation,[],[f39])).
% 19.81/2.99  
% 19.81/2.99  fof(f72,plain,(
% 19.81/2.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 19.81/2.99    inference(equality_resolution,[],[f45])).
% 19.81/2.99  
% 19.81/2.99  fof(f46,plain,(
% 19.81/2.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 19.81/2.99    inference(cnf_transformation,[],[f39])).
% 19.81/2.99  
% 19.81/2.99  fof(f71,plain,(
% 19.81/2.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 19.81/2.99    inference(equality_resolution,[],[f46])).
% 19.81/2.99  
% 19.81/2.99  fof(f1,axiom,(
% 19.81/2.99    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 19.81/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.81/2.99  
% 19.81/2.99  fof(f18,plain,(
% 19.81/2.99    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 19.81/2.99    inference(ennf_transformation,[],[f1])).
% 19.81/2.99  
% 19.81/2.99  fof(f43,plain,(
% 19.81/2.99    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 19.81/2.99    inference(cnf_transformation,[],[f18])).
% 19.81/2.99  
% 19.81/2.99  fof(f59,plain,(
% 19.81/2.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 19.81/2.99    inference(cnf_transformation,[],[f40])).
% 19.81/2.99  
% 19.81/2.99  fof(f76,plain,(
% 19.81/2.99    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 19.81/2.99    inference(equality_resolution,[],[f59])).
% 19.81/2.99  
% 19.81/2.99  cnf(c_25,negated_conjecture,
% 19.81/2.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 19.81/2.99      inference(cnf_transformation,[],[f67]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_635,plain,
% 19.81/2.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 19.81/2.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_21,plain,
% 19.81/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.81/2.99      | ~ v1_funct_1(X0)
% 19.81/2.99      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 19.81/2.99      inference(cnf_transformation,[],[f64]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_638,plain,
% 19.81/2.99      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 19.81/2.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 19.81/2.99      | v1_funct_1(X2) != iProver_top ),
% 19.81/2.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_4966,plain,
% 19.81/2.99      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
% 19.81/2.99      | v1_funct_1(sK3) != iProver_top ),
% 19.81/2.99      inference(superposition,[status(thm)],[c_635,c_638]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_27,negated_conjecture,
% 19.81/2.99      ( v1_funct_1(sK3) ),
% 19.81/2.99      inference(cnf_transformation,[],[f65]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_962,plain,
% 19.81/2.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 19.81/2.99      | ~ v1_funct_1(sK3)
% 19.81/2.99      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 19.81/2.99      inference(instantiation,[status(thm)],[c_21]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_1114,plain,
% 19.81/2.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 19.81/2.99      | ~ v1_funct_1(sK3)
% 19.81/2.99      | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 19.81/2.99      inference(instantiation,[status(thm)],[c_962]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_5015,plain,
% 19.81/2.99      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 19.81/2.99      inference(global_propositional_subsumption,
% 19.81/2.99                [status(thm)],
% 19.81/2.99                [c_4966,c_27,c_25,c_1114]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_19,plain,
% 19.81/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.81/2.99      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.81/2.99      | ~ v1_funct_1(X0) ),
% 19.81/2.99      inference(cnf_transformation,[],[f63]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_640,plain,
% 19.81/2.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 19.81/2.99      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 19.81/2.99      | v1_funct_1(X0) != iProver_top ),
% 19.81/2.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_5033,plain,
% 19.81/2.99      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 19.81/2.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 19.81/2.99      | v1_funct_1(sK3) != iProver_top ),
% 19.81/2.99      inference(superposition,[status(thm)],[c_5015,c_640]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_28,plain,
% 19.81/2.99      ( v1_funct_1(sK3) = iProver_top ),
% 19.81/2.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_30,plain,
% 19.81/2.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 19.81/2.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_957,plain,
% 19.81/2.99      ( m1_subset_1(k2_partfun1(X0,X1,sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 19.81/2.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 19.81/2.99      | ~ v1_funct_1(sK3) ),
% 19.81/2.99      inference(instantiation,[status(thm)],[c_19]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_1204,plain,
% 19.81/2.99      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 19.81/2.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 19.81/2.99      | ~ v1_funct_1(sK3) ),
% 19.81/2.99      inference(instantiation,[status(thm)],[c_957]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_1205,plain,
% 19.81/2.99      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 19.81/2.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 19.81/2.99      | v1_funct_1(sK3) != iProver_top ),
% 19.81/2.99      inference(predicate_to_equality,[status(thm)],[c_1204]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_227,plain,( X0 = X0 ),theory(equality) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_1773,plain,
% 19.81/2.99      ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 19.81/2.99      inference(instantiation,[status(thm)],[c_227]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_228,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_1791,plain,
% 19.81/2.99      ( X0 != X1
% 19.81/2.99      | X0 = k2_partfun1(sK0,sK1,sK3,X2)
% 19.81/2.99      | k2_partfun1(sK0,sK1,sK3,X2) != X1 ),
% 19.81/2.99      inference(instantiation,[status(thm)],[c_228]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_2467,plain,
% 19.81/2.99      ( X0 = k2_partfun1(sK0,sK1,sK3,X1)
% 19.81/2.99      | X0 != k7_relat_1(sK3,X1)
% 19.81/2.99      | k2_partfun1(sK0,sK1,sK3,X1) != k7_relat_1(sK3,X1) ),
% 19.81/2.99      inference(instantiation,[status(thm)],[c_1791]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_2886,plain,
% 19.81/2.99      ( k2_partfun1(sK0,sK1,sK3,X0) != k7_relat_1(sK3,X0)
% 19.81/2.99      | k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0)
% 19.81/2.99      | k7_relat_1(sK3,X0) != k7_relat_1(sK3,X0) ),
% 19.81/2.99      inference(instantiation,[status(thm)],[c_2467]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_2887,plain,
% 19.81/2.99      ( k7_relat_1(sK3,X0) = k7_relat_1(sK3,X0) ),
% 19.81/2.99      inference(instantiation,[status(thm)],[c_227]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_233,plain,
% 19.81/2.99      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 19.81/2.99      theory(equality) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_1534,plain,
% 19.81/2.99      ( m1_subset_1(X0,X1)
% 19.81/2.99      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,X2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 19.81/2.99      | X0 != k2_partfun1(sK0,sK1,sK3,X2)
% 19.81/2.99      | X1 != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 19.81/2.99      inference(instantiation,[status(thm)],[c_233]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_2123,plain,
% 19.81/2.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 19.81/2.99      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 19.81/2.99      | X0 != k2_partfun1(sK0,sK1,sK3,X1)
% 19.81/2.99      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 19.81/2.99      inference(instantiation,[status(thm)],[c_1534]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_4061,plain,
% 19.81/2.99      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 19.81/2.99      | m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 19.81/2.99      | k7_relat_1(sK3,X0) != k2_partfun1(sK0,sK1,sK3,X0)
% 19.81/2.99      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 19.81/2.99      inference(instantiation,[status(thm)],[c_2123]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_4067,plain,
% 19.81/2.99      ( k7_relat_1(sK3,X0) != k2_partfun1(sK0,sK1,sK3,X0)
% 19.81/2.99      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 19.81/2.99      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 19.81/2.99      | m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 19.81/2.99      inference(predicate_to_equality,[status(thm)],[c_4061]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_6809,plain,
% 19.81/2.99      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 19.81/2.99      inference(global_propositional_subsumption,
% 19.81/2.99                [status(thm)],
% 19.81/2.99                [c_5033,c_27,c_28,c_25,c_30,c_1114,c_1205,c_1773,c_2886,
% 19.81/2.99                 c_2887,c_4067]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_12,plain,
% 19.81/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.81/2.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 19.81/2.99      | ~ r1_tarski(k1_relat_1(X0),X3) ),
% 19.81/2.99      inference(cnf_transformation,[],[f55]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_647,plain,
% 19.81/2.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 19.81/2.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
% 19.81/2.99      | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
% 19.81/2.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_6822,plain,
% 19.81/2.99      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
% 19.81/2.99      | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X1) != iProver_top ),
% 19.81/2.99      inference(superposition,[status(thm)],[c_6809,c_647]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_24,negated_conjecture,
% 19.81/2.99      ( r1_tarski(sK2,sK0) ),
% 19.81/2.99      inference(cnf_transformation,[],[f68]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_636,plain,
% 19.81/2.99      ( r1_tarski(sK2,sK0) = iProver_top ),
% 19.81/2.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_18,plain,
% 19.81/2.99      ( ~ v1_funct_2(X0,X1,X2)
% 19.81/2.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.81/2.99      | k1_relset_1(X1,X2,X0) = X1
% 19.81/2.99      | k1_xboole_0 = X2 ),
% 19.81/2.99      inference(cnf_transformation,[],[f56]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_641,plain,
% 19.81/2.99      ( k1_relset_1(X0,X1,X2) = X0
% 19.81/2.99      | k1_xboole_0 = X1
% 19.81/2.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 19.81/2.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 19.81/2.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_2372,plain,
% 19.81/2.99      ( k1_relset_1(sK0,sK1,sK3) = sK0
% 19.81/2.99      | sK1 = k1_xboole_0
% 19.81/2.99      | v1_funct_2(sK3,sK0,sK1) != iProver_top ),
% 19.81/2.99      inference(superposition,[status(thm)],[c_635,c_641]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_11,plain,
% 19.81/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.81/2.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 19.81/2.99      inference(cnf_transformation,[],[f54]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_648,plain,
% 19.81/2.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 19.81/2.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 19.81/2.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_1848,plain,
% 19.81/2.99      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 19.81/2.99      inference(superposition,[status(thm)],[c_635,c_648]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_2386,plain,
% 19.81/2.99      ( k1_relat_1(sK3) = sK0
% 19.81/2.99      | sK1 = k1_xboole_0
% 19.81/2.99      | v1_funct_2(sK3,sK0,sK1) != iProver_top ),
% 19.81/2.99      inference(demodulation,[status(thm)],[c_2372,c_1848]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_26,negated_conjecture,
% 19.81/2.99      ( v1_funct_2(sK3,sK0,sK1) ),
% 19.81/2.99      inference(cnf_transformation,[],[f66]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_29,plain,
% 19.81/2.99      ( v1_funct_2(sK3,sK0,sK1) = iProver_top ),
% 19.81/2.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_2900,plain,
% 19.81/2.99      ( sK1 = k1_xboole_0 | k1_relat_1(sK3) = sK0 ),
% 19.81/2.99      inference(global_propositional_subsumption,[status(thm)],[c_2386,c_29]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_2901,plain,
% 19.81/2.99      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 19.81/2.99      inference(renaming,[status(thm)],[c_2900]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_8,plain,
% 19.81/2.99      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 19.81/2.99      | ~ v1_relat_1(X1)
% 19.81/2.99      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 19.81/2.99      inference(cnf_transformation,[],[f51]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_651,plain,
% 19.81/2.99      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 19.81/2.99      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 19.81/2.99      | v1_relat_1(X0) != iProver_top ),
% 19.81/2.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_2904,plain,
% 19.81/2.99      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 19.81/2.99      | sK1 = k1_xboole_0
% 19.81/2.99      | r1_tarski(X0,sK0) != iProver_top
% 19.81/2.99      | v1_relat_1(sK3) != iProver_top ),
% 19.81/2.99      inference(superposition,[status(thm)],[c_2901,c_651]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_9,plain,
% 19.81/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 19.81/2.99      inference(cnf_transformation,[],[f52]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_891,plain,
% 19.81/2.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 19.81/2.99      | v1_relat_1(sK3) ),
% 19.81/2.99      inference(instantiation,[status(thm)],[c_9]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_892,plain,
% 19.81/2.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 19.81/2.99      | v1_relat_1(sK3) = iProver_top ),
% 19.81/2.99      inference(predicate_to_equality,[status(thm)],[c_891]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_3062,plain,
% 19.81/2.99      ( r1_tarski(X0,sK0) != iProver_top
% 19.81/2.99      | sK1 = k1_xboole_0
% 19.81/2.99      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 19.81/2.99      inference(global_propositional_subsumption,
% 19.81/2.99                [status(thm)],
% 19.81/2.99                [c_2904,c_30,c_892]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_3063,plain,
% 19.81/2.99      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 19.81/2.99      | sK1 = k1_xboole_0
% 19.81/2.99      | r1_tarski(X0,sK0) != iProver_top ),
% 19.81/2.99      inference(renaming,[status(thm)],[c_3062]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_3070,plain,
% 19.81/2.99      ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 | sK1 = k1_xboole_0 ),
% 19.81/2.99      inference(superposition,[status(thm)],[c_636,c_3063]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_650,plain,
% 19.81/2.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 19.81/2.99      | v1_relat_1(X0) = iProver_top ),
% 19.81/2.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_1370,plain,
% 19.81/2.99      ( v1_relat_1(sK3) = iProver_top ),
% 19.81/2.99      inference(superposition,[status(thm)],[c_635,c_650]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_7,plain,
% 19.81/2.99      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 19.81/2.99      inference(cnf_transformation,[],[f50]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_652,plain,
% 19.81/2.99      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
% 19.81/2.99      | v1_relat_1(X0) != iProver_top ),
% 19.81/2.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_10,plain,
% 19.81/2.99      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 19.81/2.99      inference(cnf_transformation,[],[f53]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_649,plain,
% 19.81/2.99      ( v4_relat_1(X0,X1) = iProver_top
% 19.81/2.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 19.81/2.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_8304,plain,
% 19.81/2.99      ( v4_relat_1(k7_relat_1(sK3,X0),X1) = iProver_top
% 19.81/2.99      | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X1) != iProver_top ),
% 19.81/2.99      inference(superposition,[status(thm)],[c_6822,c_649]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_10186,plain,
% 19.81/2.99      ( v4_relat_1(k7_relat_1(sK3,X0),X0) = iProver_top
% 19.81/2.99      | v1_relat_1(sK3) != iProver_top ),
% 19.81/2.99      inference(superposition,[status(thm)],[c_652,c_8304]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_11401,plain,
% 19.81/2.99      ( v4_relat_1(k7_relat_1(sK3,X0),X0) = iProver_top ),
% 19.81/2.99      inference(global_propositional_subsumption,
% 19.81/2.99                [status(thm)],
% 19.81/2.99                [c_10186,c_30,c_892]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_6,plain,
% 19.81/2.99      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 19.81/2.99      inference(cnf_transformation,[],[f49]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_653,plain,
% 19.81/2.99      ( k7_relat_1(X0,X1) = X0
% 19.81/2.99      | v4_relat_1(X0,X1) != iProver_top
% 19.81/2.99      | v1_relat_1(X0) != iProver_top ),
% 19.81/2.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_11408,plain,
% 19.81/2.99      ( k7_relat_1(k7_relat_1(sK3,X0),X0) = k7_relat_1(sK3,X0)
% 19.81/2.99      | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
% 19.81/2.99      inference(superposition,[status(thm)],[c_11401,c_653]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_1657,plain,
% 19.81/2.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 19.81/2.99      | v1_funct_1(X0) != iProver_top
% 19.81/2.99      | v1_relat_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
% 19.81/2.99      inference(superposition,[status(thm)],[c_640,c_650]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_6096,plain,
% 19.81/2.99      ( v1_funct_1(sK3) != iProver_top
% 19.81/2.99      | v1_relat_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
% 19.81/2.99      inference(superposition,[status(thm)],[c_635,c_1657]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_6108,plain,
% 19.81/2.99      ( v1_funct_1(sK3) != iProver_top
% 19.81/2.99      | v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 19.81/2.99      inference(light_normalisation,[status(thm)],[c_6096,c_5015]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_11588,plain,
% 19.81/2.99      ( k7_relat_1(k7_relat_1(sK3,X0),X0) = k7_relat_1(sK3,X0) ),
% 19.81/2.99      inference(global_propositional_subsumption,
% 19.81/2.99                [status(thm)],
% 19.81/2.99                [c_11408,c_28,c_6108]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_11592,plain,
% 19.81/2.99      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X0) = iProver_top
% 19.81/2.99      | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
% 19.81/2.99      inference(superposition,[status(thm)],[c_11588,c_652]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_998,plain,
% 19.81/2.99      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X0) | ~ v1_relat_1(sK3) ),
% 19.81/2.99      inference(instantiation,[status(thm)],[c_7]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_999,plain,
% 19.81/2.99      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X0) = iProver_top
% 19.81/2.99      | v1_relat_1(sK3) != iProver_top ),
% 19.81/2.99      inference(predicate_to_equality,[status(thm)],[c_998]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_11603,plain,
% 19.81/2.99      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X0) = iProver_top ),
% 19.81/2.99      inference(global_propositional_subsumption,
% 19.81/2.99                [status(thm)],
% 19.81/2.99                [c_11592,c_30,c_892,c_999]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_11618,plain,
% 19.81/2.99      ( k1_relat_1(k7_relat_1(X0,k1_relat_1(k7_relat_1(sK3,k1_relat_1(X0))))) = k1_relat_1(k7_relat_1(sK3,k1_relat_1(X0)))
% 19.81/2.99      | v1_relat_1(X0) != iProver_top ),
% 19.81/2.99      inference(superposition,[status(thm)],[c_11603,c_651]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_12650,plain,
% 19.81/2.99      ( k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3))))) = k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3))) ),
% 19.81/2.99      inference(superposition,[status(thm)],[c_1370,c_11618]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_12673,plain,
% 19.81/2.99      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))),X0)) = X0
% 19.81/2.99      | r1_tarski(X0,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))) != iProver_top
% 19.81/2.99      | v1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3))))) != iProver_top ),
% 19.81/2.99      inference(superposition,[status(thm)],[c_12650,c_651]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_6441,plain,
% 19.81/2.99      ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 19.81/2.99      inference(global_propositional_subsumption,[status(thm)],[c_6108,c_28]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_14791,plain,
% 19.81/2.99      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))),X0)) = X0
% 19.81/2.99      | r1_tarski(X0,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))) != iProver_top ),
% 19.81/2.99      inference(forward_subsumption_resolution,[status(thm)],[c_12673,c_6441]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_14801,plain,
% 19.81/2.99      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))),X0)) = X0
% 19.81/2.99      | sK1 = k1_xboole_0
% 19.81/2.99      | r1_tarski(X0,k1_relat_1(k7_relat_1(sK3,sK0))) != iProver_top ),
% 19.81/2.99      inference(superposition,[status(thm)],[c_2901,c_14791]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_1701,plain,
% 19.81/2.99      ( v4_relat_1(sK3,sK0) = iProver_top ),
% 19.81/2.99      inference(superposition,[status(thm)],[c_635,c_649]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_2285,plain,
% 19.81/2.99      ( k7_relat_1(sK3,sK0) = sK3 | v1_relat_1(sK3) != iProver_top ),
% 19.81/2.99      inference(superposition,[status(thm)],[c_1701,c_653]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_918,plain,
% 19.81/2.99      ( v4_relat_1(sK3,sK0)
% 19.81/2.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 19.81/2.99      inference(instantiation,[status(thm)],[c_10]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_1012,plain,
% 19.81/2.99      ( ~ v4_relat_1(sK3,sK0) | ~ v1_relat_1(sK3) | k7_relat_1(sK3,sK0) = sK3 ),
% 19.81/2.99      inference(instantiation,[status(thm)],[c_6]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_2685,plain,
% 19.81/2.99      ( k7_relat_1(sK3,sK0) = sK3 ),
% 19.81/2.99      inference(global_propositional_subsumption,
% 19.81/2.99                [status(thm)],
% 19.81/2.99                [c_2285,c_25,c_891,c_918,c_1012]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_14805,plain,
% 19.81/2.99      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))),X0)) = X0
% 19.81/2.99      | sK1 = k1_xboole_0
% 19.81/2.99      | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top ),
% 19.81/2.99      inference(light_normalisation,[status(thm)],[c_14801,c_2685]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_15956,plain,
% 19.81/2.99      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))),X0)) = X0
% 19.81/2.99      | sK1 = k1_xboole_0
% 19.81/2.99      | r1_tarski(X0,sK0) != iProver_top ),
% 19.81/2.99      inference(superposition,[status(thm)],[c_2901,c_14805]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_16219,plain,
% 19.81/2.99      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))),sK2)) = sK2
% 19.81/2.99      | sK1 = k1_xboole_0 ),
% 19.81/2.99      inference(superposition,[status(thm)],[c_636,c_15956]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_2516,plain,
% 19.81/2.99      ( k1_relat_1(k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))) = k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))
% 19.81/2.99      | v1_relat_1(X1) != iProver_top
% 19.81/2.99      | v1_relat_1(X0) != iProver_top ),
% 19.81/2.99      inference(superposition,[status(thm)],[c_652,c_651]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_30318,plain,
% 19.81/2.99      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),k1_relat_1(k7_relat_1(X1,k1_relat_1(k7_relat_1(sK3,X0)))))) = k1_relat_1(k7_relat_1(X1,k1_relat_1(k7_relat_1(sK3,X0))))
% 19.81/2.99      | v1_relat_1(X1) != iProver_top ),
% 19.81/2.99      inference(superposition,[status(thm)],[c_6441,c_2516]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_31051,plain,
% 19.81/2.99      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),k1_relat_1(k7_relat_1(k7_relat_1(sK3,X1),k1_relat_1(k7_relat_1(sK3,X0)))))) = k1_relat_1(k7_relat_1(k7_relat_1(sK3,X1),k1_relat_1(k7_relat_1(sK3,X0)))) ),
% 19.81/2.99      inference(superposition,[status(thm)],[c_6441,c_30318]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_31509,plain,
% 19.81/2.99      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),sK2)))) = k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),k1_relat_1(k7_relat_1(sK3,sK2))))
% 19.81/2.99      | sK1 = k1_xboole_0 ),
% 19.81/2.99      inference(superposition,[status(thm)],[c_3070,c_31051]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_3096,plain,
% 19.81/2.99      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),X0)) = X0
% 19.81/2.99      | sK1 = k1_xboole_0
% 19.81/2.99      | r1_tarski(X0,sK2) != iProver_top
% 19.81/2.99      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 19.81/2.99      inference(superposition,[status(thm)],[c_3070,c_651]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_6452,plain,
% 19.81/2.99      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),X0)) = X0
% 19.81/2.99      | sK1 = k1_xboole_0
% 19.81/2.99      | r1_tarski(X0,sK2) != iProver_top ),
% 19.81/2.99      inference(superposition,[status(thm)],[c_6441,c_3096]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_10967,plain,
% 19.81/2.99      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),k1_relat_1(k7_relat_1(X0,sK2)))) = k1_relat_1(k7_relat_1(X0,sK2))
% 19.81/2.99      | sK1 = k1_xboole_0
% 19.81/2.99      | v1_relat_1(X0) != iProver_top ),
% 19.81/2.99      inference(superposition,[status(thm)],[c_652,c_6452]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_20315,plain,
% 19.81/2.99      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),sK2)))) = k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),sK2))
% 19.81/2.99      | sK1 = k1_xboole_0 ),
% 19.81/2.99      inference(superposition,[status(thm)],[c_6441,c_10967]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_31656,plain,
% 19.81/2.99      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),k1_relat_1(k7_relat_1(sK3,sK2)))) = k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),sK2))
% 19.81/2.99      | sK1 = k1_xboole_0 ),
% 19.81/2.99      inference(superposition,[status(thm)],[c_31509,c_20315]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_33809,plain,
% 19.81/2.99      ( sK1 = k1_xboole_0
% 19.81/2.99      | r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),sK2)),k1_relat_1(k7_relat_1(sK3,sK2))) = iProver_top
% 19.81/2.99      | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
% 19.81/2.99      inference(superposition,[status(thm)],[c_31656,c_652]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_37280,plain,
% 19.81/2.99      ( r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),sK2)),k1_relat_1(k7_relat_1(sK3,sK2))) = iProver_top
% 19.81/2.99      | sK1 = k1_xboole_0 ),
% 19.81/2.99      inference(global_propositional_subsumption,
% 19.81/2.99                [status(thm)],
% 19.81/2.99                [c_33809,c_28,c_6108]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_37281,plain,
% 19.81/2.99      ( sK1 = k1_xboole_0
% 19.81/2.99      | r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),sK2)),k1_relat_1(k7_relat_1(sK3,sK2))) = iProver_top ),
% 19.81/2.99      inference(renaming,[status(thm)],[c_37280]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_37291,plain,
% 19.81/2.99      ( sK1 = k1_xboole_0
% 19.81/2.99      | r1_tarski(sK2,k1_relat_1(k7_relat_1(sK3,sK2))) = iProver_top ),
% 19.81/2.99      inference(superposition,[status(thm)],[c_16219,c_37281]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_8301,plain,
% 19.81/2.99      ( k1_relset_1(X0,sK1,k7_relat_1(sK3,X1)) = k1_relat_1(k7_relat_1(sK3,X1))
% 19.81/2.99      | r1_tarski(k1_relat_1(k7_relat_1(sK3,X1)),X0) != iProver_top ),
% 19.81/2.99      inference(superposition,[status(thm)],[c_6822,c_648]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_13857,plain,
% 19.81/2.99      ( k1_relset_1(X0,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
% 19.81/2.99      | sK1 = k1_xboole_0
% 19.81/2.99      | r1_tarski(sK2,X0) != iProver_top ),
% 19.81/2.99      inference(superposition,[status(thm)],[c_3070,c_8301]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_37560,plain,
% 19.81/2.99      ( k1_relset_1(k1_relat_1(k7_relat_1(sK3,sK2)),sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
% 19.81/2.99      | sK1 = k1_xboole_0 ),
% 19.81/2.99      inference(superposition,[status(thm)],[c_37291,c_13857]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_16,plain,
% 19.81/2.99      ( v1_funct_2(X0,X1,X2)
% 19.81/2.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.81/2.99      | k1_relset_1(X1,X2,X0) != X1
% 19.81/2.99      | k1_xboole_0 = X2 ),
% 19.81/2.99      inference(cnf_transformation,[],[f58]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_643,plain,
% 19.81/2.99      ( k1_relset_1(X0,X1,X2) != X0
% 19.81/2.99      | k1_xboole_0 = X1
% 19.81/2.99      | v1_funct_2(X2,X0,X1) = iProver_top
% 19.81/2.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 19.81/2.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_39295,plain,
% 19.81/2.99      ( sK1 = k1_xboole_0
% 19.81/2.99      | v1_funct_2(k7_relat_1(sK3,sK2),k1_relat_1(k7_relat_1(sK3,sK2)),sK1) = iProver_top
% 19.81/2.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,sK2)),sK1))) != iProver_top ),
% 19.81/2.99      inference(superposition,[status(thm)],[c_37560,c_643]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_72970,plain,
% 19.81/2.99      ( sK1 = k1_xboole_0
% 19.81/2.99      | v1_funct_2(k7_relat_1(sK3,sK2),k1_relat_1(k7_relat_1(sK3,sK2)),sK1) = iProver_top
% 19.81/2.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 19.81/2.99      inference(superposition,[status(thm)],[c_3070,c_39295]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_22,negated_conjecture,
% 19.81/2.99      ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
% 19.81/2.99      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 19.81/2.99      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 19.81/2.99      inference(cnf_transformation,[],[f70]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_637,plain,
% 19.81/2.99      ( v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) != iProver_top
% 19.81/2.99      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 19.81/2.99      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 19.81/2.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_5019,plain,
% 19.81/2.99      ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) != iProver_top
% 19.81/2.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 19.81/2.99      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 19.81/2.99      inference(demodulation,[status(thm)],[c_5015,c_637]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_20,plain,
% 19.81/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.81/2.99      | ~ v1_funct_1(X0)
% 19.81/2.99      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 19.81/2.99      inference(cnf_transformation,[],[f62]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_639,plain,
% 19.81/2.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 19.81/2.99      | v1_funct_1(X0) != iProver_top
% 19.81/2.99      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
% 19.81/2.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_1041,plain,
% 19.81/2.99      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 19.81/2.99      | v1_funct_1(sK3) != iProver_top ),
% 19.81/2.99      inference(superposition,[status(thm)],[c_635,c_639]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_1300,plain,
% 19.81/2.99      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
% 19.81/2.99      inference(global_propositional_subsumption,[status(thm)],[c_1041,c_28]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_5020,plain,
% 19.81/2.99      ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 19.81/2.99      inference(demodulation,[status(thm)],[c_5015,c_1300]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_5026,plain,
% 19.81/2.99      ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) != iProver_top
% 19.81/2.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 19.81/2.99      inference(forward_subsumption_resolution,[status(thm)],[c_5019,c_5020]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_3095,plain,
% 19.81/2.99      ( sK1 = k1_xboole_0
% 19.81/2.99      | r1_tarski(sK2,sK2) = iProver_top
% 19.81/2.99      | v1_relat_1(sK3) != iProver_top ),
% 19.81/2.99      inference(superposition,[status(thm)],[c_3070,c_652]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_3257,plain,
% 19.81/2.99      ( r1_tarski(sK2,sK2) = iProver_top | sK1 = k1_xboole_0 ),
% 19.81/2.99      inference(global_propositional_subsumption,
% 19.81/2.99                [status(thm)],
% 19.81/2.99                [c_3095,c_30,c_892]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_3258,plain,
% 19.81/2.99      ( sK1 = k1_xboole_0 | r1_tarski(sK2,sK2) = iProver_top ),
% 19.81/2.99      inference(renaming,[status(thm)],[c_3257]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_14129,plain,
% 19.81/2.99      ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
% 19.81/2.99      | sK1 = k1_xboole_0 ),
% 19.81/2.99      inference(superposition,[status(thm)],[c_3258,c_13857]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_15053,plain,
% 19.81/2.99      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 19.81/2.99      | sK1 = k1_xboole_0
% 19.81/2.99      | v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) = iProver_top
% 19.81/2.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 19.81/2.99      inference(superposition,[status(thm)],[c_14129,c_643]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_73604,plain,
% 19.81/2.99      ( sK1 = k1_xboole_0
% 19.81/2.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 19.81/2.99      inference(global_propositional_subsumption,
% 19.81/2.99                [status(thm)],
% 19.81/2.99                [c_72970,c_3070,c_5026,c_15053]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_73611,plain,
% 19.81/2.99      ( sK1 = k1_xboole_0
% 19.81/2.99      | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) != iProver_top ),
% 19.81/2.99      inference(superposition,[status(thm)],[c_6822,c_73604]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_73820,plain,
% 19.81/2.99      ( sK1 = k1_xboole_0 ),
% 19.81/2.99      inference(forward_subsumption_resolution,[status(thm)],[c_73611,c_11603]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_73933,plain,
% 19.81/2.99      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
% 19.81/2.99      inference(demodulation,[status(thm)],[c_73820,c_6809]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_23,negated_conjecture,
% 19.81/2.99      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 19.81/2.99      inference(cnf_transformation,[],[f69]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_73947,plain,
% 19.81/2.99      ( sK0 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 19.81/2.99      inference(demodulation,[status(thm)],[c_73820,c_23]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_73948,plain,
% 19.81/2.99      ( sK0 = k1_xboole_0 ),
% 19.81/2.99      inference(equality_resolution_simp,[status(thm)],[c_73947]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_73988,plain,
% 19.81/2.99      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 19.81/2.99      inference(light_normalisation,[status(thm)],[c_73933,c_73948]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_2,plain,
% 19.81/2.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 19.81/2.99      inference(cnf_transformation,[],[f72]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_73990,plain,
% 19.81/2.99      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 19.81/2.99      inference(demodulation,[status(thm)],[c_73988,c_2]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_73937,plain,
% 19.81/2.99      ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,k1_xboole_0) != iProver_top
% 19.81/2.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 19.81/2.99      inference(demodulation,[status(thm)],[c_73820,c_5026]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_1,plain,
% 19.81/2.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 19.81/2.99      inference(cnf_transformation,[],[f71]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_73973,plain,
% 19.81/2.99      ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,k1_xboole_0) != iProver_top
% 19.81/2.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 19.81/2.99      inference(demodulation,[status(thm)],[c_73937,c_1]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_73992,plain,
% 19.81/2.99      ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,k1_xboole_0) != iProver_top ),
% 19.81/2.99      inference(backward_subsumption_resolution,
% 19.81/2.99                [status(thm)],
% 19.81/2.99                [c_73990,c_73973]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_74158,plain,
% 19.81/2.99      ( k7_relat_1(sK3,k1_xboole_0) = sK3 ),
% 19.81/2.99      inference(demodulation,[status(thm)],[c_73948,c_2685]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_74160,plain,
% 19.81/2.99      ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 19.81/2.99      inference(demodulation,[status(thm)],[c_73948,c_636]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_0,plain,
% 19.81/2.99      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 19.81/2.99      inference(cnf_transformation,[],[f43]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_656,plain,
% 19.81/2.99      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 19.81/2.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_74532,plain,
% 19.81/2.99      ( sK2 = k1_xboole_0 ),
% 19.81/2.99      inference(superposition,[status(thm)],[c_74160,c_656]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_82138,plain,
% 19.81/2.99      ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 19.81/2.99      inference(light_normalisation,[status(thm)],[c_73992,c_74158,c_74532]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_8297,plain,
% 19.81/2.99      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 19.81/2.99      | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_xboole_0) != iProver_top ),
% 19.81/2.99      inference(superposition,[status(thm)],[c_2,c_6822]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_8687,plain,
% 19.81/2.99      ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 19.81/2.99      | v1_relat_1(sK3) != iProver_top ),
% 19.81/2.99      inference(superposition,[status(thm)],[c_652,c_8297]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_1001,plain,
% 19.81/2.99      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,k1_xboole_0)),k1_xboole_0) = iProver_top
% 19.81/2.99      | v1_relat_1(sK3) != iProver_top ),
% 19.81/2.99      inference(instantiation,[status(thm)],[c_999]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_8354,plain,
% 19.81/2.99      ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 19.81/2.99      | r1_tarski(k1_relat_1(k7_relat_1(sK3,k1_xboole_0)),k1_xboole_0) != iProver_top ),
% 19.81/2.99      inference(instantiation,[status(thm)],[c_8297]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_8738,plain,
% 19.81/2.99      ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 19.81/2.99      inference(global_propositional_subsumption,
% 19.81/2.99                [status(thm)],
% 19.81/2.99                [c_8687,c_30,c_892,c_1001,c_8354]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_1850,plain,
% 19.81/2.99      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
% 19.81/2.99      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 19.81/2.99      inference(superposition,[status(thm)],[c_2,c_648]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_8746,plain,
% 19.81/2.99      ( k1_relset_1(k1_xboole_0,X0,k7_relat_1(sK3,k1_xboole_0)) = k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) ),
% 19.81/2.99      inference(superposition,[status(thm)],[c_8738,c_1850]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_1466,plain,
% 19.81/2.99      ( k1_relat_1(k7_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 19.81/2.99      | v1_relat_1(X0) != iProver_top ),
% 19.81/2.99      inference(superposition,[status(thm)],[c_652,c_656]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_1570,plain,
% 19.81/2.99      ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
% 19.81/2.99      inference(superposition,[status(thm)],[c_1370,c_1466]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_8757,plain,
% 19.81/2.99      ( k1_relset_1(k1_xboole_0,X0,k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
% 19.81/2.99      inference(light_normalisation,[status(thm)],[c_8746,c_1570]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_15,plain,
% 19.81/2.99      ( v1_funct_2(X0,k1_xboole_0,X1)
% 19.81/2.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 19.81/2.99      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 19.81/2.99      inference(cnf_transformation,[],[f76]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_644,plain,
% 19.81/2.99      ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
% 19.81/2.99      | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
% 19.81/2.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 19.81/2.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_739,plain,
% 19.81/2.99      ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
% 19.81/2.99      | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
% 19.81/2.99      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 19.81/2.99      inference(light_normalisation,[status(thm)],[c_644,c_2]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_9242,plain,
% 19.81/2.99      ( v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,X0) = iProver_top
% 19.81/2.99      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 19.81/2.99      inference(superposition,[status(thm)],[c_8757,c_739]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_12532,plain,
% 19.81/2.99      ( v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,X0) = iProver_top ),
% 19.81/2.99      inference(global_propositional_subsumption,
% 19.81/2.99                [status(thm)],
% 19.81/2.99                [c_9242,c_30,c_892,c_1001,c_8354]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_75166,plain,
% 19.81/2.99      ( v1_funct_2(sK3,k1_xboole_0,X0) = iProver_top ),
% 19.81/2.99      inference(demodulation,[status(thm)],[c_74158,c_12532]) ).
% 19.81/2.99  
% 19.81/2.99  cnf(c_82140,plain,
% 19.81/2.99      ( $false ),
% 19.81/2.99      inference(forward_subsumption_resolution,[status(thm)],[c_82138,c_75166]) ).
% 19.81/2.99  
% 19.81/2.99  
% 19.81/2.99  % SZS output end CNFRefutation for theBenchmark.p
% 19.81/2.99  
% 19.81/2.99  ------                               Statistics
% 19.81/2.99  
% 19.81/2.99  ------ Selected
% 19.81/2.99  
% 19.81/2.99  total_time:                             2.421
% 19.81/2.99  
%------------------------------------------------------------------------------
