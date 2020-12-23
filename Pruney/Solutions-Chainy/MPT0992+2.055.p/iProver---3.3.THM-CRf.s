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
% DateTime   : Thu Dec  3 12:03:57 EST 2020

% Result     : Theorem 11.17s
% Output     : CNFRefutation 11.17s
% Verified   : 
% Statistics : Number of formulae       :  251 (3988 expanded)
%              Number of clauses        :  173 (1454 expanded)
%              Number of leaves         :   20 ( 714 expanded)
%              Depth                    :   28
%              Number of atoms          :  716 (20943 expanded)
%              Number of equality atoms :  421 (6613 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
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

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f42,plain,
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

fof(f43,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f35,f42])).

fof(f72,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f24])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( r1_tarski(X0,X3)
       => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f26])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f73,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f13,axiom,(
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

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f71,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f77,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f44])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f70,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f75,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f43])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f83,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f64])).

fof(f4,axiom,(
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
    inference(nnf_transformation,[],[f4])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f38])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f79,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f66])).

fof(f81,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f80])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f78,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f51])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f74,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f43])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f46,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f48,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1474,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1480,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4101,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1474,c_1480])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X3,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1479,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(X3,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4631,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(k1_relat_1(sK3),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4101,c_1479])).

cnf(c_28,negated_conjecture,
    ( r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1475,plain,
    ( r1_tarski(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_526,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_30])).

cnf(c_527,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_526])).

cnf(c_529,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_527,c_29])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1481,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3055,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1474,c_1481])).

cnf(c_3390,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_529,c_3055])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1483,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4250,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3390,c_1483])).

cnf(c_34,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1714,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1715,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1714])).

cnf(c_8785,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | sK1 = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4250,c_34,c_1715])).

cnf(c_8786,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_8785])).

cnf(c_8797,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1475,c_8786])).

cnf(c_11,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1484,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1490,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3010,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1474,c_1479])).

cnf(c_4102,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3010,c_1480])).

cnf(c_6181,plain,
    ( k1_relset_1(X0,sK1,X1) = k1_relat_1(X1)
    | r1_tarski(X1,sK3) != iProver_top
    | r1_tarski(k1_relat_1(X1),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4102,c_1481])).

cnf(c_17174,plain,
    ( k1_relset_1(k1_relat_1(X0),sK1,X0) = k1_relat_1(X0)
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1490,c_6181])).

cnf(c_22527,plain,
    ( k1_relset_1(k1_relat_1(k7_relat_1(sK3,X0)),sK1,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0))
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1484,c_17174])).

cnf(c_40054,plain,
    ( k1_relset_1(k1_relat_1(k7_relat_1(sK3,X0)),sK1,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_22527,c_34,c_1715])).

cnf(c_40059,plain,
    ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8797,c_40054])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1476,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_7107,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1474,c_1476])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_32,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_7345,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7107,c_32])).

cnf(c_20,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_26,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_510,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relset_1(X1,X2,X0) != X1
    | sK2 != X1
    | sK1 != X2
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_26])).

cnf(c_511,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_510])).

cnf(c_1468,plain,
    ( k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | k1_xboole_0 = sK1
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_511])).

cnf(c_7352,plain,
    ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) != sK2
    | sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7345,c_1468])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1477,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1906,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1474,c_1477])).

cnf(c_2084,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1906,c_32])).

cnf(c_7353,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7345,c_2084])).

cnf(c_7360,plain,
    ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) != sK2
    | sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7352,c_7353])).

cnf(c_40416,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_40059,c_7360])).

cnf(c_40692,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_40416,c_8797])).

cnf(c_40701,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
    | r1_tarski(k1_relat_1(sK3),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4631,c_40692])).

cnf(c_868,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1997,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_868])).

cnf(c_5179,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_870,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1784,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(X2),X3)
    | X3 != X1
    | k1_relat_1(X2) != X0 ),
    inference(instantiation,[status(thm)],[c_870])).

cnf(c_2515,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X2)
    | X2 != X1
    | k1_relat_1(k7_relat_1(sK3,X0)) != X0 ),
    inference(instantiation,[status(thm)],[c_1784])).

cnf(c_4562,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),sK2)
    | k1_relat_1(k7_relat_1(sK3,X0)) != X0
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_2515])).

cnf(c_11047,plain,
    ( ~ r1_tarski(X0,sK2)
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),sK2)
    | k1_relat_1(k7_relat_1(sK3,X0)) != X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_4562])).

cnf(c_38982,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
    | ~ r1_tarski(sK2,sK2)
    | k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_11047])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1478,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_7397,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7345,c_1478])).

cnf(c_1820,plain,
    ( r1_tarski(k7_relat_1(sK3,X0),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1821,plain,
    ( r1_tarski(k7_relat_1(sK3,X0),sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1820])).

cnf(c_1774,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ r1_tarski(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1982,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ r1_tarski(k7_relat_1(sK3,X0),sK3) ),
    inference(instantiation,[status(thm)],[c_1774])).

cnf(c_1983,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | r1_tarski(k7_relat_1(sK3,X0),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1982])).

cnf(c_7778,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7397,c_34,c_1715,c_1821,c_1983])).

cnf(c_7788,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_7778,c_1480])).

cnf(c_40703,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7788,c_40692])).

cnf(c_40725,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
    | sK1 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_40703])).

cnf(c_40899,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_40701,c_1997,c_5179,c_8797,c_38982,c_40725])).

cnf(c_19,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_478,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | sK2 != k1_xboole_0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_26])).

cnf(c_479,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_478])).

cnf(c_1470,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_479])).

cnf(c_6,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1633,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1470,c_6])).

cnf(c_2143,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1633,c_2084])).

cnf(c_7349,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7345,c_2143])).

cnf(c_41028,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_40899,c_7349])).

cnf(c_17,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_432,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 != X0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_26])).

cnf(c_433,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_432])).

cnf(c_1472,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_433])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1620,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1472,c_5])).

cnf(c_8,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_84,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_86,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_84])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_92,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_94,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_92])).

cnf(c_2126,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | sK1 != k1_xboole_0
    | sK2 = k1_xboole_0
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1620,c_86,c_94])).

cnf(c_2127,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2126])).

cnf(c_2135,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2127,c_2084])).

cnf(c_7350,plain,
    ( k7_relat_1(sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7345,c_2135])).

cnf(c_27,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_87,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_88,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1730,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK2)
    | sK2 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_869,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2615,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_869])).

cnf(c_2616,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2615])).

cnf(c_1936,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_870])).

cnf(c_2833,plain,
    ( ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1936])).

cnf(c_5194,plain,
    ( ~ r1_tarski(sK2,sK0)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2833])).

cnf(c_5492,plain,
    ( r1_tarski(k1_xboole_0,sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_8263,plain,
    ( sK1 != k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7350,c_28,c_27,c_87,c_88,c_1730,c_1997,c_2616,c_5194,c_5492])).

cnf(c_8264,plain,
    ( sK2 = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_8263])).

cnf(c_41029,plain,
    ( sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_40899,c_8264])).

cnf(c_41218,plain,
    ( sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_41029])).

cnf(c_41228,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_41028,c_41218])).

cnf(c_41229,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_41228])).

cnf(c_41031,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_40899,c_7778])).

cnf(c_41060,plain,
    ( sK0 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_40899,c_27])).

cnf(c_41061,plain,
    ( sK0 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_41060])).

cnf(c_41212,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_41031,c_41061])).

cnf(c_41214,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_41212,c_6])).

cnf(c_41233,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_41229,c_41214])).

cnf(c_1489,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_8795,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1489,c_8786])).

cnf(c_1814,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1816,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1814])).

cnf(c_2041,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_9273,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8795,c_29,c_1714,c_1816,c_2041])).

cnf(c_12851,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_7788])).

cnf(c_13192,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9273,c_12851])).

cnf(c_1823,plain,
    ( r1_tarski(k7_relat_1(sK3,k1_xboole_0),sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1821])).

cnf(c_6179,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_4102])).

cnf(c_9276,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k7_relat_1(sK3,k1_xboole_0),sK3) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9273,c_6179])).

cnf(c_19714,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13192,c_34,c_94,c_1715,c_1823,c_9276])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1486,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_19719,plain,
    ( r1_tarski(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_19714,c_1486])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1488,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_19821,plain,
    ( k7_relat_1(sK3,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_19719,c_1488])).

cnf(c_41234,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_41233,c_19821])).

cnf(c_1487,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3057,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_1481])).

cnf(c_3194,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
    | r1_tarski(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1487,c_3057])).

cnf(c_12502,plain,
    ( k1_relset_1(k1_xboole_0,X0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1490,c_3194])).

cnf(c_41235,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_41234,c_6,c_12502])).

cnf(c_10,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1485,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2415,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_1485])).

cnf(c_4248,plain,
    ( k1_relat_1(k7_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1489,c_1483])).

cnf(c_10901,plain,
    ( k1_relat_1(k7_relat_1(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2415,c_4248])).

cnf(c_2586,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1484,c_1488])).

cnf(c_1775,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1774])).

cnf(c_1777,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1775])).

cnf(c_1846,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1847,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1846])).

cnf(c_1849,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1847])).

cnf(c_1966,plain,
    ( r1_tarski(k1_xboole_0,sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1969,plain,
    ( r1_tarski(k1_xboole_0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1966])).

cnf(c_2739,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2586,c_34,c_1777,c_1849,c_1969])).

cnf(c_10907,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_10901,c_2739])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_41235,c_10907,c_94,c_86])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:27:29 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.35  % Running in FOF mode
% 11.17/2.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.17/2.00  
% 11.17/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.17/2.00  
% 11.17/2.00  ------  iProver source info
% 11.17/2.00  
% 11.17/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.17/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.17/2.00  git: non_committed_changes: false
% 11.17/2.00  git: last_make_outside_of_git: false
% 11.17/2.00  
% 11.17/2.00  ------ 
% 11.17/2.00  
% 11.17/2.00  ------ Input Options
% 11.17/2.00  
% 11.17/2.00  --out_options                           all
% 11.17/2.00  --tptp_safe_out                         true
% 11.17/2.00  --problem_path                          ""
% 11.17/2.00  --include_path                          ""
% 11.17/2.00  --clausifier                            res/vclausify_rel
% 11.17/2.00  --clausifier_options                    --mode clausify
% 11.17/2.00  --stdin                                 false
% 11.17/2.00  --stats_out                             all
% 11.17/2.00  
% 11.17/2.00  ------ General Options
% 11.17/2.00  
% 11.17/2.00  --fof                                   false
% 11.17/2.00  --time_out_real                         305.
% 11.17/2.00  --time_out_virtual                      -1.
% 11.17/2.00  --symbol_type_check                     false
% 11.17/2.00  --clausify_out                          false
% 11.17/2.00  --sig_cnt_out                           false
% 11.17/2.00  --trig_cnt_out                          false
% 11.17/2.00  --trig_cnt_out_tolerance                1.
% 11.17/2.00  --trig_cnt_out_sk_spl                   false
% 11.17/2.00  --abstr_cl_out                          false
% 11.17/2.00  
% 11.17/2.00  ------ Global Options
% 11.17/2.00  
% 11.17/2.00  --schedule                              default
% 11.17/2.00  --add_important_lit                     false
% 11.17/2.00  --prop_solver_per_cl                    1000
% 11.17/2.00  --min_unsat_core                        false
% 11.17/2.00  --soft_assumptions                      false
% 11.17/2.00  --soft_lemma_size                       3
% 11.17/2.00  --prop_impl_unit_size                   0
% 11.17/2.00  --prop_impl_unit                        []
% 11.17/2.00  --share_sel_clauses                     true
% 11.17/2.00  --reset_solvers                         false
% 11.17/2.00  --bc_imp_inh                            [conj_cone]
% 11.17/2.00  --conj_cone_tolerance                   3.
% 11.17/2.00  --extra_neg_conj                        none
% 11.17/2.00  --large_theory_mode                     true
% 11.17/2.00  --prolific_symb_bound                   200
% 11.17/2.00  --lt_threshold                          2000
% 11.17/2.00  --clause_weak_htbl                      true
% 11.17/2.00  --gc_record_bc_elim                     false
% 11.17/2.00  
% 11.17/2.00  ------ Preprocessing Options
% 11.17/2.00  
% 11.17/2.00  --preprocessing_flag                    true
% 11.17/2.00  --time_out_prep_mult                    0.1
% 11.17/2.00  --splitting_mode                        input
% 11.17/2.00  --splitting_grd                         true
% 11.17/2.00  --splitting_cvd                         false
% 11.17/2.00  --splitting_cvd_svl                     false
% 11.17/2.00  --splitting_nvd                         32
% 11.17/2.00  --sub_typing                            true
% 11.17/2.00  --prep_gs_sim                           true
% 11.17/2.00  --prep_unflatten                        true
% 11.17/2.00  --prep_res_sim                          true
% 11.17/2.00  --prep_upred                            true
% 11.17/2.00  --prep_sem_filter                       exhaustive
% 11.17/2.00  --prep_sem_filter_out                   false
% 11.17/2.00  --pred_elim                             true
% 11.17/2.00  --res_sim_input                         true
% 11.17/2.00  --eq_ax_congr_red                       true
% 11.17/2.00  --pure_diseq_elim                       true
% 11.17/2.00  --brand_transform                       false
% 11.17/2.00  --non_eq_to_eq                          false
% 11.17/2.00  --prep_def_merge                        true
% 11.17/2.00  --prep_def_merge_prop_impl              false
% 11.17/2.00  --prep_def_merge_mbd                    true
% 11.17/2.00  --prep_def_merge_tr_red                 false
% 11.17/2.00  --prep_def_merge_tr_cl                  false
% 11.17/2.00  --smt_preprocessing                     true
% 11.17/2.00  --smt_ac_axioms                         fast
% 11.17/2.00  --preprocessed_out                      false
% 11.17/2.00  --preprocessed_stats                    false
% 11.17/2.00  
% 11.17/2.00  ------ Abstraction refinement Options
% 11.17/2.00  
% 11.17/2.00  --abstr_ref                             []
% 11.17/2.00  --abstr_ref_prep                        false
% 11.17/2.00  --abstr_ref_until_sat                   false
% 11.17/2.00  --abstr_ref_sig_restrict                funpre
% 11.17/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.17/2.00  --abstr_ref_under                       []
% 11.17/2.00  
% 11.17/2.00  ------ SAT Options
% 11.17/2.00  
% 11.17/2.00  --sat_mode                              false
% 11.17/2.00  --sat_fm_restart_options                ""
% 11.17/2.00  --sat_gr_def                            false
% 11.17/2.00  --sat_epr_types                         true
% 11.17/2.00  --sat_non_cyclic_types                  false
% 11.17/2.00  --sat_finite_models                     false
% 11.17/2.00  --sat_fm_lemmas                         false
% 11.17/2.00  --sat_fm_prep                           false
% 11.17/2.00  --sat_fm_uc_incr                        true
% 11.17/2.00  --sat_out_model                         small
% 11.17/2.00  --sat_out_clauses                       false
% 11.17/2.00  
% 11.17/2.00  ------ QBF Options
% 11.17/2.00  
% 11.17/2.00  --qbf_mode                              false
% 11.17/2.00  --qbf_elim_univ                         false
% 11.17/2.00  --qbf_dom_inst                          none
% 11.17/2.00  --qbf_dom_pre_inst                      false
% 11.17/2.00  --qbf_sk_in                             false
% 11.17/2.00  --qbf_pred_elim                         true
% 11.17/2.00  --qbf_split                             512
% 11.17/2.00  
% 11.17/2.00  ------ BMC1 Options
% 11.17/2.00  
% 11.17/2.00  --bmc1_incremental                      false
% 11.17/2.00  --bmc1_axioms                           reachable_all
% 11.17/2.00  --bmc1_min_bound                        0
% 11.17/2.00  --bmc1_max_bound                        -1
% 11.17/2.00  --bmc1_max_bound_default                -1
% 11.17/2.00  --bmc1_symbol_reachability              true
% 11.17/2.00  --bmc1_property_lemmas                  false
% 11.17/2.00  --bmc1_k_induction                      false
% 11.17/2.00  --bmc1_non_equiv_states                 false
% 11.17/2.00  --bmc1_deadlock                         false
% 11.17/2.00  --bmc1_ucm                              false
% 11.17/2.00  --bmc1_add_unsat_core                   none
% 11.17/2.00  --bmc1_unsat_core_children              false
% 11.17/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.17/2.00  --bmc1_out_stat                         full
% 11.17/2.00  --bmc1_ground_init                      false
% 11.17/2.00  --bmc1_pre_inst_next_state              false
% 11.17/2.00  --bmc1_pre_inst_state                   false
% 11.17/2.00  --bmc1_pre_inst_reach_state             false
% 11.17/2.00  --bmc1_out_unsat_core                   false
% 11.17/2.00  --bmc1_aig_witness_out                  false
% 11.17/2.00  --bmc1_verbose                          false
% 11.17/2.00  --bmc1_dump_clauses_tptp                false
% 11.17/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.17/2.00  --bmc1_dump_file                        -
% 11.17/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.17/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.17/2.00  --bmc1_ucm_extend_mode                  1
% 11.17/2.00  --bmc1_ucm_init_mode                    2
% 11.17/2.00  --bmc1_ucm_cone_mode                    none
% 11.17/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.17/2.00  --bmc1_ucm_relax_model                  4
% 11.17/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.17/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.17/2.00  --bmc1_ucm_layered_model                none
% 11.17/2.00  --bmc1_ucm_max_lemma_size               10
% 11.17/2.00  
% 11.17/2.00  ------ AIG Options
% 11.17/2.00  
% 11.17/2.00  --aig_mode                              false
% 11.17/2.00  
% 11.17/2.00  ------ Instantiation Options
% 11.17/2.00  
% 11.17/2.00  --instantiation_flag                    true
% 11.17/2.00  --inst_sos_flag                         false
% 11.17/2.00  --inst_sos_phase                        true
% 11.17/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.17/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.17/2.00  --inst_lit_sel_side                     num_symb
% 11.17/2.00  --inst_solver_per_active                1400
% 11.17/2.00  --inst_solver_calls_frac                1.
% 11.17/2.00  --inst_passive_queue_type               priority_queues
% 11.17/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.17/2.00  --inst_passive_queues_freq              [25;2]
% 11.17/2.00  --inst_dismatching                      true
% 11.17/2.00  --inst_eager_unprocessed_to_passive     true
% 11.17/2.00  --inst_prop_sim_given                   true
% 11.17/2.00  --inst_prop_sim_new                     false
% 11.17/2.00  --inst_subs_new                         false
% 11.17/2.00  --inst_eq_res_simp                      false
% 11.17/2.00  --inst_subs_given                       false
% 11.17/2.00  --inst_orphan_elimination               true
% 11.17/2.00  --inst_learning_loop_flag               true
% 11.17/2.00  --inst_learning_start                   3000
% 11.17/2.00  --inst_learning_factor                  2
% 11.17/2.00  --inst_start_prop_sim_after_learn       3
% 11.17/2.00  --inst_sel_renew                        solver
% 11.17/2.00  --inst_lit_activity_flag                true
% 11.17/2.00  --inst_restr_to_given                   false
% 11.17/2.00  --inst_activity_threshold               500
% 11.17/2.00  --inst_out_proof                        true
% 11.17/2.00  
% 11.17/2.00  ------ Resolution Options
% 11.17/2.00  
% 11.17/2.00  --resolution_flag                       true
% 11.17/2.00  --res_lit_sel                           adaptive
% 11.17/2.00  --res_lit_sel_side                      none
% 11.17/2.00  --res_ordering                          kbo
% 11.17/2.00  --res_to_prop_solver                    active
% 11.17/2.00  --res_prop_simpl_new                    false
% 11.17/2.00  --res_prop_simpl_given                  true
% 11.17/2.00  --res_passive_queue_type                priority_queues
% 11.17/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.17/2.00  --res_passive_queues_freq               [15;5]
% 11.17/2.00  --res_forward_subs                      full
% 11.17/2.00  --res_backward_subs                     full
% 11.17/2.00  --res_forward_subs_resolution           true
% 11.17/2.00  --res_backward_subs_resolution          true
% 11.17/2.00  --res_orphan_elimination                true
% 11.17/2.00  --res_time_limit                        2.
% 11.17/2.00  --res_out_proof                         true
% 11.17/2.00  
% 11.17/2.00  ------ Superposition Options
% 11.17/2.00  
% 11.17/2.00  --superposition_flag                    true
% 11.17/2.00  --sup_passive_queue_type                priority_queues
% 11.17/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.17/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.17/2.00  --demod_completeness_check              fast
% 11.17/2.00  --demod_use_ground                      true
% 11.17/2.00  --sup_to_prop_solver                    passive
% 11.17/2.00  --sup_prop_simpl_new                    true
% 11.17/2.00  --sup_prop_simpl_given                  true
% 11.17/2.00  --sup_fun_splitting                     false
% 11.17/2.00  --sup_smt_interval                      50000
% 11.17/2.00  
% 11.17/2.00  ------ Superposition Simplification Setup
% 11.17/2.00  
% 11.17/2.00  --sup_indices_passive                   []
% 11.17/2.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.17/2.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.17/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.17/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.17/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.17/2.00  --sup_full_bw                           [BwDemod]
% 11.17/2.00  --sup_immed_triv                        [TrivRules]
% 11.17/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.17/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.17/2.00  --sup_immed_bw_main                     []
% 11.17/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.17/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.17/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.17/2.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.17/2.00  
% 11.17/2.00  ------ Combination Options
% 11.17/2.00  
% 11.17/2.00  --comb_res_mult                         3
% 11.17/2.00  --comb_sup_mult                         2
% 11.17/2.00  --comb_inst_mult                        10
% 11.17/2.00  
% 11.17/2.00  ------ Debug Options
% 11.17/2.00  
% 11.17/2.00  --dbg_backtrace                         false
% 11.17/2.00  --dbg_dump_prop_clauses                 false
% 11.17/2.00  --dbg_dump_prop_clauses_file            -
% 11.17/2.00  --dbg_out_stat                          false
% 11.17/2.00  ------ Parsing...
% 11.17/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.17/2.00  
% 11.17/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.17/2.00  
% 11.17/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.17/2.00  
% 11.17/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.17/2.00  ------ Proving...
% 11.17/2.00  ------ Problem Properties 
% 11.17/2.00  
% 11.17/2.00  
% 11.17/2.00  clauses                                 30
% 11.17/2.00  conjectures                             4
% 11.17/2.00  EPR                                     7
% 11.17/2.00  Horn                                    27
% 11.17/2.00  unary                                   8
% 11.17/2.00  binary                                  8
% 11.17/2.00  lits                                    74
% 11.17/2.00  lits eq                                 28
% 11.17/2.00  fd_pure                                 0
% 11.17/2.00  fd_pseudo                               0
% 11.17/2.00  fd_cond                                 2
% 11.17/2.00  fd_pseudo_cond                          1
% 11.17/2.00  AC symbols                              0
% 11.17/2.00  
% 11.17/2.00  ------ Schedule dynamic 5 is on 
% 11.17/2.00  
% 11.17/2.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.17/2.00  
% 11.17/2.00  
% 11.17/2.00  ------ 
% 11.17/2.00  Current options:
% 11.17/2.00  ------ 
% 11.17/2.00  
% 11.17/2.00  ------ Input Options
% 11.17/2.00  
% 11.17/2.00  --out_options                           all
% 11.17/2.00  --tptp_safe_out                         true
% 11.17/2.00  --problem_path                          ""
% 11.17/2.00  --include_path                          ""
% 11.17/2.00  --clausifier                            res/vclausify_rel
% 11.17/2.00  --clausifier_options                    --mode clausify
% 11.17/2.00  --stdin                                 false
% 11.17/2.00  --stats_out                             all
% 11.17/2.00  
% 11.17/2.00  ------ General Options
% 11.17/2.00  
% 11.17/2.00  --fof                                   false
% 11.17/2.00  --time_out_real                         305.
% 11.17/2.00  --time_out_virtual                      -1.
% 11.17/2.00  --symbol_type_check                     false
% 11.17/2.00  --clausify_out                          false
% 11.17/2.00  --sig_cnt_out                           false
% 11.17/2.00  --trig_cnt_out                          false
% 11.17/2.00  --trig_cnt_out_tolerance                1.
% 11.17/2.00  --trig_cnt_out_sk_spl                   false
% 11.17/2.00  --abstr_cl_out                          false
% 11.17/2.00  
% 11.17/2.00  ------ Global Options
% 11.17/2.00  
% 11.17/2.00  --schedule                              default
% 11.17/2.00  --add_important_lit                     false
% 11.17/2.00  --prop_solver_per_cl                    1000
% 11.17/2.00  --min_unsat_core                        false
% 11.17/2.00  --soft_assumptions                      false
% 11.17/2.00  --soft_lemma_size                       3
% 11.17/2.00  --prop_impl_unit_size                   0
% 11.17/2.00  --prop_impl_unit                        []
% 11.17/2.00  --share_sel_clauses                     true
% 11.17/2.00  --reset_solvers                         false
% 11.17/2.00  --bc_imp_inh                            [conj_cone]
% 11.17/2.00  --conj_cone_tolerance                   3.
% 11.17/2.00  --extra_neg_conj                        none
% 11.17/2.00  --large_theory_mode                     true
% 11.17/2.00  --prolific_symb_bound                   200
% 11.17/2.00  --lt_threshold                          2000
% 11.17/2.00  --clause_weak_htbl                      true
% 11.17/2.00  --gc_record_bc_elim                     false
% 11.17/2.00  
% 11.17/2.00  ------ Preprocessing Options
% 11.17/2.00  
% 11.17/2.00  --preprocessing_flag                    true
% 11.17/2.00  --time_out_prep_mult                    0.1
% 11.17/2.00  --splitting_mode                        input
% 11.17/2.00  --splitting_grd                         true
% 11.17/2.00  --splitting_cvd                         false
% 11.17/2.00  --splitting_cvd_svl                     false
% 11.17/2.00  --splitting_nvd                         32
% 11.17/2.00  --sub_typing                            true
% 11.17/2.00  --prep_gs_sim                           true
% 11.17/2.00  --prep_unflatten                        true
% 11.17/2.00  --prep_res_sim                          true
% 11.17/2.00  --prep_upred                            true
% 11.17/2.00  --prep_sem_filter                       exhaustive
% 11.17/2.00  --prep_sem_filter_out                   false
% 11.17/2.00  --pred_elim                             true
% 11.17/2.00  --res_sim_input                         true
% 11.17/2.00  --eq_ax_congr_red                       true
% 11.17/2.00  --pure_diseq_elim                       true
% 11.17/2.00  --brand_transform                       false
% 11.17/2.00  --non_eq_to_eq                          false
% 11.17/2.00  --prep_def_merge                        true
% 11.17/2.00  --prep_def_merge_prop_impl              false
% 11.17/2.00  --prep_def_merge_mbd                    true
% 11.17/2.00  --prep_def_merge_tr_red                 false
% 11.17/2.00  --prep_def_merge_tr_cl                  false
% 11.17/2.00  --smt_preprocessing                     true
% 11.17/2.00  --smt_ac_axioms                         fast
% 11.17/2.00  --preprocessed_out                      false
% 11.17/2.00  --preprocessed_stats                    false
% 11.17/2.00  
% 11.17/2.00  ------ Abstraction refinement Options
% 11.17/2.00  
% 11.17/2.00  --abstr_ref                             []
% 11.17/2.00  --abstr_ref_prep                        false
% 11.17/2.00  --abstr_ref_until_sat                   false
% 11.17/2.00  --abstr_ref_sig_restrict                funpre
% 11.17/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.17/2.00  --abstr_ref_under                       []
% 11.17/2.00  
% 11.17/2.00  ------ SAT Options
% 11.17/2.00  
% 11.17/2.00  --sat_mode                              false
% 11.17/2.00  --sat_fm_restart_options                ""
% 11.17/2.00  --sat_gr_def                            false
% 11.17/2.00  --sat_epr_types                         true
% 11.17/2.00  --sat_non_cyclic_types                  false
% 11.17/2.00  --sat_finite_models                     false
% 11.17/2.00  --sat_fm_lemmas                         false
% 11.17/2.00  --sat_fm_prep                           false
% 11.17/2.00  --sat_fm_uc_incr                        true
% 11.17/2.00  --sat_out_model                         small
% 11.17/2.00  --sat_out_clauses                       false
% 11.17/2.00  
% 11.17/2.00  ------ QBF Options
% 11.17/2.00  
% 11.17/2.00  --qbf_mode                              false
% 11.17/2.00  --qbf_elim_univ                         false
% 11.17/2.00  --qbf_dom_inst                          none
% 11.17/2.00  --qbf_dom_pre_inst                      false
% 11.17/2.00  --qbf_sk_in                             false
% 11.17/2.00  --qbf_pred_elim                         true
% 11.17/2.00  --qbf_split                             512
% 11.17/2.00  
% 11.17/2.00  ------ BMC1 Options
% 11.17/2.00  
% 11.17/2.00  --bmc1_incremental                      false
% 11.17/2.00  --bmc1_axioms                           reachable_all
% 11.17/2.00  --bmc1_min_bound                        0
% 11.17/2.00  --bmc1_max_bound                        -1
% 11.17/2.00  --bmc1_max_bound_default                -1
% 11.17/2.00  --bmc1_symbol_reachability              true
% 11.17/2.00  --bmc1_property_lemmas                  false
% 11.17/2.00  --bmc1_k_induction                      false
% 11.17/2.00  --bmc1_non_equiv_states                 false
% 11.17/2.00  --bmc1_deadlock                         false
% 11.17/2.00  --bmc1_ucm                              false
% 11.17/2.00  --bmc1_add_unsat_core                   none
% 11.17/2.00  --bmc1_unsat_core_children              false
% 11.17/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.17/2.00  --bmc1_out_stat                         full
% 11.17/2.00  --bmc1_ground_init                      false
% 11.17/2.00  --bmc1_pre_inst_next_state              false
% 11.17/2.00  --bmc1_pre_inst_state                   false
% 11.17/2.00  --bmc1_pre_inst_reach_state             false
% 11.17/2.00  --bmc1_out_unsat_core                   false
% 11.17/2.00  --bmc1_aig_witness_out                  false
% 11.17/2.00  --bmc1_verbose                          false
% 11.17/2.00  --bmc1_dump_clauses_tptp                false
% 11.17/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.17/2.00  --bmc1_dump_file                        -
% 11.17/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.17/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.17/2.00  --bmc1_ucm_extend_mode                  1
% 11.17/2.00  --bmc1_ucm_init_mode                    2
% 11.17/2.00  --bmc1_ucm_cone_mode                    none
% 11.17/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.17/2.00  --bmc1_ucm_relax_model                  4
% 11.17/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.17/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.17/2.00  --bmc1_ucm_layered_model                none
% 11.17/2.00  --bmc1_ucm_max_lemma_size               10
% 11.17/2.00  
% 11.17/2.00  ------ AIG Options
% 11.17/2.00  
% 11.17/2.00  --aig_mode                              false
% 11.17/2.00  
% 11.17/2.00  ------ Instantiation Options
% 11.17/2.00  
% 11.17/2.00  --instantiation_flag                    true
% 11.17/2.00  --inst_sos_flag                         false
% 11.17/2.00  --inst_sos_phase                        true
% 11.17/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.17/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.17/2.00  --inst_lit_sel_side                     none
% 11.17/2.00  --inst_solver_per_active                1400
% 11.17/2.00  --inst_solver_calls_frac                1.
% 11.17/2.00  --inst_passive_queue_type               priority_queues
% 11.17/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.17/2.00  --inst_passive_queues_freq              [25;2]
% 11.17/2.00  --inst_dismatching                      true
% 11.17/2.00  --inst_eager_unprocessed_to_passive     true
% 11.17/2.00  --inst_prop_sim_given                   true
% 11.17/2.00  --inst_prop_sim_new                     false
% 11.17/2.00  --inst_subs_new                         false
% 11.17/2.00  --inst_eq_res_simp                      false
% 11.17/2.00  --inst_subs_given                       false
% 11.17/2.00  --inst_orphan_elimination               true
% 11.17/2.00  --inst_learning_loop_flag               true
% 11.17/2.00  --inst_learning_start                   3000
% 11.17/2.00  --inst_learning_factor                  2
% 11.17/2.00  --inst_start_prop_sim_after_learn       3
% 11.17/2.00  --inst_sel_renew                        solver
% 11.17/2.00  --inst_lit_activity_flag                true
% 11.17/2.00  --inst_restr_to_given                   false
% 11.17/2.00  --inst_activity_threshold               500
% 11.17/2.00  --inst_out_proof                        true
% 11.17/2.00  
% 11.17/2.00  ------ Resolution Options
% 11.17/2.00  
% 11.17/2.00  --resolution_flag                       false
% 11.17/2.00  --res_lit_sel                           adaptive
% 11.17/2.00  --res_lit_sel_side                      none
% 11.17/2.00  --res_ordering                          kbo
% 11.17/2.00  --res_to_prop_solver                    active
% 11.17/2.00  --res_prop_simpl_new                    false
% 11.17/2.00  --res_prop_simpl_given                  true
% 11.17/2.00  --res_passive_queue_type                priority_queues
% 11.17/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.17/2.00  --res_passive_queues_freq               [15;5]
% 11.17/2.00  --res_forward_subs                      full
% 11.17/2.00  --res_backward_subs                     full
% 11.17/2.00  --res_forward_subs_resolution           true
% 11.17/2.00  --res_backward_subs_resolution          true
% 11.17/2.00  --res_orphan_elimination                true
% 11.17/2.00  --res_time_limit                        2.
% 11.17/2.00  --res_out_proof                         true
% 11.17/2.00  
% 11.17/2.00  ------ Superposition Options
% 11.17/2.00  
% 11.17/2.00  --superposition_flag                    true
% 11.17/2.00  --sup_passive_queue_type                priority_queues
% 11.17/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.17/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.17/2.00  --demod_completeness_check              fast
% 11.17/2.00  --demod_use_ground                      true
% 11.17/2.00  --sup_to_prop_solver                    passive
% 11.17/2.00  --sup_prop_simpl_new                    true
% 11.17/2.00  --sup_prop_simpl_given                  true
% 11.17/2.00  --sup_fun_splitting                     false
% 11.17/2.00  --sup_smt_interval                      50000
% 11.17/2.00  
% 11.17/2.00  ------ Superposition Simplification Setup
% 11.17/2.00  
% 11.17/2.00  --sup_indices_passive                   []
% 11.17/2.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.17/2.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.17/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.17/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.17/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.17/2.00  --sup_full_bw                           [BwDemod]
% 11.17/2.00  --sup_immed_triv                        [TrivRules]
% 11.17/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.17/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.17/2.00  --sup_immed_bw_main                     []
% 11.17/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.17/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.17/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.17/2.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.17/2.00  
% 11.17/2.00  ------ Combination Options
% 11.17/2.00  
% 11.17/2.00  --comb_res_mult                         3
% 11.17/2.00  --comb_sup_mult                         2
% 11.17/2.00  --comb_inst_mult                        10
% 11.17/2.00  
% 11.17/2.00  ------ Debug Options
% 11.17/2.00  
% 11.17/2.00  --dbg_backtrace                         false
% 11.17/2.00  --dbg_dump_prop_clauses                 false
% 11.17/2.00  --dbg_dump_prop_clauses_file            -
% 11.17/2.00  --dbg_out_stat                          false
% 11.17/2.00  
% 11.17/2.00  
% 11.17/2.00  
% 11.17/2.00  
% 11.17/2.00  ------ Proving...
% 11.17/2.00  
% 11.17/2.00  
% 11.17/2.00  % SZS status Theorem for theBenchmark.p
% 11.17/2.00  
% 11.17/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.17/2.00  
% 11.17/2.00  fof(f16,conjecture,(
% 11.17/2.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 11.17/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.17/2.00  
% 11.17/2.00  fof(f17,negated_conjecture,(
% 11.17/2.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 11.17/2.00    inference(negated_conjecture,[],[f16])).
% 11.17/2.00  
% 11.17/2.00  fof(f34,plain,(
% 11.17/2.00    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 11.17/2.00    inference(ennf_transformation,[],[f17])).
% 11.17/2.00  
% 11.17/2.00  fof(f35,plain,(
% 11.17/2.00    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 11.17/2.00    inference(flattening,[],[f34])).
% 11.17/2.00  
% 11.17/2.00  fof(f42,plain,(
% 11.17/2.00    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 11.17/2.00    introduced(choice_axiom,[])).
% 11.17/2.00  
% 11.17/2.00  fof(f43,plain,(
% 11.17/2.00    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 11.17/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f35,f42])).
% 11.17/2.00  
% 11.17/2.00  fof(f72,plain,(
% 11.17/2.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 11.17/2.00    inference(cnf_transformation,[],[f43])).
% 11.17/2.00  
% 11.17/2.00  fof(f11,axiom,(
% 11.17/2.00    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 11.17/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.17/2.00  
% 11.17/2.00  fof(f24,plain,(
% 11.17/2.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 11.17/2.00    inference(ennf_transformation,[],[f11])).
% 11.17/2.00  
% 11.17/2.00  fof(f25,plain,(
% 11.17/2.00    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 11.17/2.00    inference(flattening,[],[f24])).
% 11.17/2.00  
% 11.17/2.00  fof(f59,plain,(
% 11.17/2.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 11.17/2.00    inference(cnf_transformation,[],[f25])).
% 11.17/2.00  
% 11.17/2.00  fof(f12,axiom,(
% 11.17/2.00    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => (r1_tarski(X0,X3) => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 11.17/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.17/2.00  
% 11.17/2.00  fof(f26,plain,(
% 11.17/2.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 11.17/2.00    inference(ennf_transformation,[],[f12])).
% 11.17/2.00  
% 11.17/2.00  fof(f27,plain,(
% 11.17/2.00    ! [X0,X1,X2,X3] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 11.17/2.00    inference(flattening,[],[f26])).
% 11.17/2.00  
% 11.17/2.00  fof(f60,plain,(
% 11.17/2.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 11.17/2.00    inference(cnf_transformation,[],[f27])).
% 11.17/2.00  
% 11.17/2.00  fof(f73,plain,(
% 11.17/2.00    r1_tarski(sK2,sK0)),
% 11.17/2.00    inference(cnf_transformation,[],[f43])).
% 11.17/2.00  
% 11.17/2.00  fof(f13,axiom,(
% 11.17/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 11.17/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.17/2.00  
% 11.17/2.00  fof(f28,plain,(
% 11.17/2.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.17/2.01    inference(ennf_transformation,[],[f13])).
% 11.17/2.01  
% 11.17/2.01  fof(f29,plain,(
% 11.17/2.01    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.17/2.01    inference(flattening,[],[f28])).
% 11.17/2.01  
% 11.17/2.01  fof(f41,plain,(
% 11.17/2.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.17/2.01    inference(nnf_transformation,[],[f29])).
% 11.17/2.01  
% 11.17/2.01  fof(f61,plain,(
% 11.17/2.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.17/2.01    inference(cnf_transformation,[],[f41])).
% 11.17/2.01  
% 11.17/2.01  fof(f71,plain,(
% 11.17/2.01    v1_funct_2(sK3,sK0,sK1)),
% 11.17/2.01    inference(cnf_transformation,[],[f43])).
% 11.17/2.01  
% 11.17/2.01  fof(f10,axiom,(
% 11.17/2.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 11.17/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.17/2.01  
% 11.17/2.01  fof(f23,plain,(
% 11.17/2.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.17/2.01    inference(ennf_transformation,[],[f10])).
% 11.17/2.01  
% 11.17/2.01  fof(f58,plain,(
% 11.17/2.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.17/2.01    inference(cnf_transformation,[],[f23])).
% 11.17/2.01  
% 11.17/2.01  fof(f8,axiom,(
% 11.17/2.01    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 11.17/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.17/2.01  
% 11.17/2.01  fof(f20,plain,(
% 11.17/2.01    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 11.17/2.01    inference(ennf_transformation,[],[f8])).
% 11.17/2.01  
% 11.17/2.01  fof(f21,plain,(
% 11.17/2.01    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 11.17/2.01    inference(flattening,[],[f20])).
% 11.17/2.01  
% 11.17/2.01  fof(f56,plain,(
% 11.17/2.01    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 11.17/2.01    inference(cnf_transformation,[],[f21])).
% 11.17/2.01  
% 11.17/2.01  fof(f9,axiom,(
% 11.17/2.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 11.17/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.17/2.01  
% 11.17/2.01  fof(f22,plain,(
% 11.17/2.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.17/2.01    inference(ennf_transformation,[],[f9])).
% 11.17/2.01  
% 11.17/2.01  fof(f57,plain,(
% 11.17/2.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.17/2.01    inference(cnf_transformation,[],[f22])).
% 11.17/2.01  
% 11.17/2.01  fof(f7,axiom,(
% 11.17/2.01    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 11.17/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.17/2.01  
% 11.17/2.01  fof(f19,plain,(
% 11.17/2.01    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 11.17/2.01    inference(ennf_transformation,[],[f7])).
% 11.17/2.01  
% 11.17/2.01  fof(f55,plain,(
% 11.17/2.01    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 11.17/2.01    inference(cnf_transformation,[],[f19])).
% 11.17/2.01  
% 11.17/2.01  fof(f1,axiom,(
% 11.17/2.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.17/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.17/2.01  
% 11.17/2.01  fof(f36,plain,(
% 11.17/2.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.17/2.01    inference(nnf_transformation,[],[f1])).
% 11.17/2.01  
% 11.17/2.01  fof(f37,plain,(
% 11.17/2.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.17/2.01    inference(flattening,[],[f36])).
% 11.17/2.01  
% 11.17/2.01  fof(f44,plain,(
% 11.17/2.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 11.17/2.01    inference(cnf_transformation,[],[f37])).
% 11.17/2.01  
% 11.17/2.01  fof(f77,plain,(
% 11.17/2.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.17/2.01    inference(equality_resolution,[],[f44])).
% 11.17/2.01  
% 11.17/2.01  fof(f15,axiom,(
% 11.17/2.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 11.17/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.17/2.01  
% 11.17/2.01  fof(f32,plain,(
% 11.17/2.01    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 11.17/2.01    inference(ennf_transformation,[],[f15])).
% 11.17/2.01  
% 11.17/2.01  fof(f33,plain,(
% 11.17/2.01    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 11.17/2.01    inference(flattening,[],[f32])).
% 11.17/2.01  
% 11.17/2.01  fof(f69,plain,(
% 11.17/2.01    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 11.17/2.01    inference(cnf_transformation,[],[f33])).
% 11.17/2.01  
% 11.17/2.01  fof(f70,plain,(
% 11.17/2.01    v1_funct_1(sK3)),
% 11.17/2.01    inference(cnf_transformation,[],[f43])).
% 11.17/2.01  
% 11.17/2.01  fof(f63,plain,(
% 11.17/2.01    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.17/2.01    inference(cnf_transformation,[],[f41])).
% 11.17/2.01  
% 11.17/2.01  fof(f75,plain,(
% 11.17/2.01    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 11.17/2.01    inference(cnf_transformation,[],[f43])).
% 11.17/2.01  
% 11.17/2.01  fof(f14,axiom,(
% 11.17/2.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 11.17/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.17/2.01  
% 11.17/2.01  fof(f30,plain,(
% 11.17/2.01    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 11.17/2.01    inference(ennf_transformation,[],[f14])).
% 11.17/2.01  
% 11.17/2.01  fof(f31,plain,(
% 11.17/2.01    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 11.17/2.01    inference(flattening,[],[f30])).
% 11.17/2.01  
% 11.17/2.01  fof(f67,plain,(
% 11.17/2.01    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 11.17/2.01    inference(cnf_transformation,[],[f31])).
% 11.17/2.01  
% 11.17/2.01  fof(f68,plain,(
% 11.17/2.01    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 11.17/2.01    inference(cnf_transformation,[],[f31])).
% 11.17/2.01  
% 11.17/2.01  fof(f64,plain,(
% 11.17/2.01    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.17/2.01    inference(cnf_transformation,[],[f41])).
% 11.17/2.01  
% 11.17/2.01  fof(f83,plain,(
% 11.17/2.01    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 11.17/2.01    inference(equality_resolution,[],[f64])).
% 11.17/2.01  
% 11.17/2.01  fof(f4,axiom,(
% 11.17/2.01    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 11.17/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.17/2.01  
% 11.17/2.01  fof(f38,plain,(
% 11.17/2.01    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 11.17/2.01    inference(nnf_transformation,[],[f4])).
% 11.17/2.01  
% 11.17/2.01  fof(f39,plain,(
% 11.17/2.01    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 11.17/2.01    inference(flattening,[],[f38])).
% 11.17/2.01  
% 11.17/2.01  fof(f50,plain,(
% 11.17/2.01    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 11.17/2.01    inference(cnf_transformation,[],[f39])).
% 11.17/2.01  
% 11.17/2.01  fof(f79,plain,(
% 11.17/2.01    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 11.17/2.01    inference(equality_resolution,[],[f50])).
% 11.17/2.01  
% 11.17/2.01  fof(f66,plain,(
% 11.17/2.01    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.17/2.01    inference(cnf_transformation,[],[f41])).
% 11.17/2.01  
% 11.17/2.01  fof(f80,plain,(
% 11.17/2.01    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.17/2.01    inference(equality_resolution,[],[f66])).
% 11.17/2.01  
% 11.17/2.01  fof(f81,plain,(
% 11.17/2.01    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 11.17/2.01    inference(equality_resolution,[],[f80])).
% 11.17/2.01  
% 11.17/2.01  fof(f51,plain,(
% 11.17/2.01    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 11.17/2.01    inference(cnf_transformation,[],[f39])).
% 11.17/2.01  
% 11.17/2.01  fof(f78,plain,(
% 11.17/2.01    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 11.17/2.01    inference(equality_resolution,[],[f51])).
% 11.17/2.01  
% 11.17/2.01  fof(f5,axiom,(
% 11.17/2.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 11.17/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.17/2.01  
% 11.17/2.01  fof(f40,plain,(
% 11.17/2.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 11.17/2.01    inference(nnf_transformation,[],[f5])).
% 11.17/2.01  
% 11.17/2.01  fof(f53,plain,(
% 11.17/2.01    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 11.17/2.01    inference(cnf_transformation,[],[f40])).
% 11.17/2.01  
% 11.17/2.01  fof(f2,axiom,(
% 11.17/2.01    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 11.17/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.17/2.01  
% 11.17/2.01  fof(f47,plain,(
% 11.17/2.01    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 11.17/2.01    inference(cnf_transformation,[],[f2])).
% 11.17/2.01  
% 11.17/2.01  fof(f74,plain,(
% 11.17/2.01    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 11.17/2.01    inference(cnf_transformation,[],[f43])).
% 11.17/2.01  
% 11.17/2.01  fof(f49,plain,(
% 11.17/2.01    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 11.17/2.01    inference(cnf_transformation,[],[f39])).
% 11.17/2.01  
% 11.17/2.01  fof(f46,plain,(
% 11.17/2.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.17/2.01    inference(cnf_transformation,[],[f37])).
% 11.17/2.01  
% 11.17/2.01  fof(f52,plain,(
% 11.17/2.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 11.17/2.01    inference(cnf_transformation,[],[f40])).
% 11.17/2.01  
% 11.17/2.01  fof(f3,axiom,(
% 11.17/2.01    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 11.17/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.17/2.01  
% 11.17/2.01  fof(f18,plain,(
% 11.17/2.01    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 11.17/2.01    inference(ennf_transformation,[],[f3])).
% 11.17/2.01  
% 11.17/2.01  fof(f48,plain,(
% 11.17/2.01    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 11.17/2.01    inference(cnf_transformation,[],[f18])).
% 11.17/2.01  
% 11.17/2.01  fof(f6,axiom,(
% 11.17/2.01    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 11.17/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.17/2.01  
% 11.17/2.01  fof(f54,plain,(
% 11.17/2.01    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 11.17/2.01    inference(cnf_transformation,[],[f6])).
% 11.17/2.01  
% 11.17/2.01  cnf(c_29,negated_conjecture,
% 11.17/2.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 11.17/2.01      inference(cnf_transformation,[],[f72]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_1474,plain,
% 11.17/2.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 11.17/2.01      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_15,plain,
% 11.17/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.17/2.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 11.17/2.01      | ~ r1_tarski(k1_relat_1(X0),X3) ),
% 11.17/2.01      inference(cnf_transformation,[],[f59]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_1480,plain,
% 11.17/2.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.17/2.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
% 11.17/2.01      | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
% 11.17/2.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_4101,plain,
% 11.17/2.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) = iProver_top
% 11.17/2.01      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
% 11.17/2.01      inference(superposition,[status(thm)],[c_1474,c_1480]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_16,plain,
% 11.17/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.17/2.01      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.17/2.01      | ~ r1_tarski(X3,X0) ),
% 11.17/2.01      inference(cnf_transformation,[],[f60]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_1479,plain,
% 11.17/2.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.17/2.01      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 11.17/2.01      | r1_tarski(X3,X0) != iProver_top ),
% 11.17/2.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_4631,plain,
% 11.17/2.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
% 11.17/2.01      | r1_tarski(X0,sK3) != iProver_top
% 11.17/2.01      | r1_tarski(k1_relat_1(sK3),X1) != iProver_top ),
% 11.17/2.01      inference(superposition,[status(thm)],[c_4101,c_1479]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_28,negated_conjecture,
% 11.17/2.01      ( r1_tarski(sK2,sK0) ),
% 11.17/2.01      inference(cnf_transformation,[],[f73]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_1475,plain,
% 11.17/2.01      ( r1_tarski(sK2,sK0) = iProver_top ),
% 11.17/2.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_22,plain,
% 11.17/2.01      ( ~ v1_funct_2(X0,X1,X2)
% 11.17/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.17/2.01      | k1_relset_1(X1,X2,X0) = X1
% 11.17/2.01      | k1_xboole_0 = X2 ),
% 11.17/2.01      inference(cnf_transformation,[],[f61]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_30,negated_conjecture,
% 11.17/2.01      ( v1_funct_2(sK3,sK0,sK1) ),
% 11.17/2.01      inference(cnf_transformation,[],[f71]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_526,plain,
% 11.17/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.17/2.01      | k1_relset_1(X1,X2,X0) = X1
% 11.17/2.01      | sK3 != X0
% 11.17/2.01      | sK1 != X2
% 11.17/2.01      | sK0 != X1
% 11.17/2.01      | k1_xboole_0 = X2 ),
% 11.17/2.01      inference(resolution_lifted,[status(thm)],[c_22,c_30]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_527,plain,
% 11.17/2.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 11.17/2.01      | k1_relset_1(sK0,sK1,sK3) = sK0
% 11.17/2.01      | k1_xboole_0 = sK1 ),
% 11.17/2.01      inference(unflattening,[status(thm)],[c_526]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_529,plain,
% 11.17/2.01      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 11.17/2.01      inference(global_propositional_subsumption,
% 11.17/2.01                [status(thm)],
% 11.17/2.01                [c_527,c_29]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_14,plain,
% 11.17/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.17/2.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 11.17/2.01      inference(cnf_transformation,[],[f58]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_1481,plain,
% 11.17/2.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 11.17/2.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.17/2.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_3055,plain,
% 11.17/2.01      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 11.17/2.01      inference(superposition,[status(thm)],[c_1474,c_1481]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_3390,plain,
% 11.17/2.01      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 11.17/2.01      inference(superposition,[status(thm)],[c_529,c_3055]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_12,plain,
% 11.17/2.01      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 11.17/2.01      | ~ v1_relat_1(X1)
% 11.17/2.01      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 11.17/2.01      inference(cnf_transformation,[],[f56]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_1483,plain,
% 11.17/2.01      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 11.17/2.01      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 11.17/2.01      | v1_relat_1(X0) != iProver_top ),
% 11.17/2.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_4250,plain,
% 11.17/2.01      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 11.17/2.01      | sK1 = k1_xboole_0
% 11.17/2.01      | r1_tarski(X0,sK0) != iProver_top
% 11.17/2.01      | v1_relat_1(sK3) != iProver_top ),
% 11.17/2.01      inference(superposition,[status(thm)],[c_3390,c_1483]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_34,plain,
% 11.17/2.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 11.17/2.01      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_13,plain,
% 11.17/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.17/2.01      | v1_relat_1(X0) ),
% 11.17/2.01      inference(cnf_transformation,[],[f57]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_1714,plain,
% 11.17/2.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 11.17/2.01      | v1_relat_1(sK3) ),
% 11.17/2.01      inference(instantiation,[status(thm)],[c_13]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_1715,plain,
% 11.17/2.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 11.17/2.01      | v1_relat_1(sK3) = iProver_top ),
% 11.17/2.01      inference(predicate_to_equality,[status(thm)],[c_1714]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_8785,plain,
% 11.17/2.01      ( r1_tarski(X0,sK0) != iProver_top
% 11.17/2.01      | sK1 = k1_xboole_0
% 11.17/2.01      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 11.17/2.01      inference(global_propositional_subsumption,
% 11.17/2.01                [status(thm)],
% 11.17/2.01                [c_4250,c_34,c_1715]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_8786,plain,
% 11.17/2.01      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 11.17/2.01      | sK1 = k1_xboole_0
% 11.17/2.01      | r1_tarski(X0,sK0) != iProver_top ),
% 11.17/2.01      inference(renaming,[status(thm)],[c_8785]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_8797,plain,
% 11.17/2.01      ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 | sK1 = k1_xboole_0 ),
% 11.17/2.01      inference(superposition,[status(thm)],[c_1475,c_8786]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_11,plain,
% 11.17/2.01      ( r1_tarski(k7_relat_1(X0,X1),X0) | ~ v1_relat_1(X0) ),
% 11.17/2.01      inference(cnf_transformation,[],[f55]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_1484,plain,
% 11.17/2.01      ( r1_tarski(k7_relat_1(X0,X1),X0) = iProver_top
% 11.17/2.01      | v1_relat_1(X0) != iProver_top ),
% 11.17/2.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_2,plain,
% 11.17/2.01      ( r1_tarski(X0,X0) ),
% 11.17/2.01      inference(cnf_transformation,[],[f77]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_1490,plain,
% 11.17/2.01      ( r1_tarski(X0,X0) = iProver_top ),
% 11.17/2.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_3010,plain,
% 11.17/2.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 11.17/2.01      | r1_tarski(X0,sK3) != iProver_top ),
% 11.17/2.01      inference(superposition,[status(thm)],[c_1474,c_1479]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_4102,plain,
% 11.17/2.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
% 11.17/2.01      | r1_tarski(X0,sK3) != iProver_top
% 11.17/2.01      | r1_tarski(k1_relat_1(X0),X1) != iProver_top ),
% 11.17/2.01      inference(superposition,[status(thm)],[c_3010,c_1480]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_6181,plain,
% 11.17/2.01      ( k1_relset_1(X0,sK1,X1) = k1_relat_1(X1)
% 11.17/2.01      | r1_tarski(X1,sK3) != iProver_top
% 11.17/2.01      | r1_tarski(k1_relat_1(X1),X0) != iProver_top ),
% 11.17/2.01      inference(superposition,[status(thm)],[c_4102,c_1481]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_17174,plain,
% 11.17/2.01      ( k1_relset_1(k1_relat_1(X0),sK1,X0) = k1_relat_1(X0)
% 11.17/2.01      | r1_tarski(X0,sK3) != iProver_top ),
% 11.17/2.01      inference(superposition,[status(thm)],[c_1490,c_6181]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_22527,plain,
% 11.17/2.01      ( k1_relset_1(k1_relat_1(k7_relat_1(sK3,X0)),sK1,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0))
% 11.17/2.01      | v1_relat_1(sK3) != iProver_top ),
% 11.17/2.01      inference(superposition,[status(thm)],[c_1484,c_17174]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_40054,plain,
% 11.17/2.01      ( k1_relset_1(k1_relat_1(k7_relat_1(sK3,X0)),sK1,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
% 11.17/2.01      inference(global_propositional_subsumption,
% 11.17/2.01                [status(thm)],
% 11.17/2.01                [c_22527,c_34,c_1715]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_40059,plain,
% 11.17/2.01      ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
% 11.17/2.01      | sK1 = k1_xboole_0 ),
% 11.17/2.01      inference(superposition,[status(thm)],[c_8797,c_40054]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_25,plain,
% 11.17/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.17/2.01      | ~ v1_funct_1(X0)
% 11.17/2.01      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 11.17/2.01      inference(cnf_transformation,[],[f69]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_1476,plain,
% 11.17/2.01      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 11.17/2.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.17/2.01      | v1_funct_1(X2) != iProver_top ),
% 11.17/2.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_7107,plain,
% 11.17/2.01      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
% 11.17/2.01      | v1_funct_1(sK3) != iProver_top ),
% 11.17/2.01      inference(superposition,[status(thm)],[c_1474,c_1476]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_31,negated_conjecture,
% 11.17/2.01      ( v1_funct_1(sK3) ),
% 11.17/2.01      inference(cnf_transformation,[],[f70]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_32,plain,
% 11.17/2.01      ( v1_funct_1(sK3) = iProver_top ),
% 11.17/2.01      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_7345,plain,
% 11.17/2.01      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 11.17/2.01      inference(global_propositional_subsumption,
% 11.17/2.01                [status(thm)],
% 11.17/2.01                [c_7107,c_32]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_20,plain,
% 11.17/2.01      ( v1_funct_2(X0,X1,X2)
% 11.17/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.17/2.01      | k1_relset_1(X1,X2,X0) != X1
% 11.17/2.01      | k1_xboole_0 = X2 ),
% 11.17/2.01      inference(cnf_transformation,[],[f63]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_26,negated_conjecture,
% 11.17/2.01      ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
% 11.17/2.01      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.17/2.01      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 11.17/2.01      inference(cnf_transformation,[],[f75]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_510,plain,
% 11.17/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.17/2.01      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.17/2.01      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 11.17/2.01      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 11.17/2.01      | k1_relset_1(X1,X2,X0) != X1
% 11.17/2.01      | sK2 != X1
% 11.17/2.01      | sK1 != X2
% 11.17/2.01      | k1_xboole_0 = X2 ),
% 11.17/2.01      inference(resolution_lifted,[status(thm)],[c_20,c_26]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_511,plain,
% 11.17/2.01      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.17/2.01      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 11.17/2.01      | k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 11.17/2.01      | k1_xboole_0 = sK1 ),
% 11.17/2.01      inference(unflattening,[status(thm)],[c_510]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_1468,plain,
% 11.17/2.01      ( k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 11.17/2.01      | k1_xboole_0 = sK1
% 11.17/2.01      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 11.17/2.01      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 11.17/2.01      inference(predicate_to_equality,[status(thm)],[c_511]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_7352,plain,
% 11.17/2.01      ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) != sK2
% 11.17/2.01      | sK1 = k1_xboole_0
% 11.17/2.01      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 11.17/2.01      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 11.17/2.01      inference(demodulation,[status(thm)],[c_7345,c_1468]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_24,plain,
% 11.17/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.17/2.01      | ~ v1_funct_1(X0)
% 11.17/2.01      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 11.17/2.01      inference(cnf_transformation,[],[f67]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_1477,plain,
% 11.17/2.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.17/2.01      | v1_funct_1(X0) != iProver_top
% 11.17/2.01      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
% 11.17/2.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_1906,plain,
% 11.17/2.01      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 11.17/2.01      | v1_funct_1(sK3) != iProver_top ),
% 11.17/2.01      inference(superposition,[status(thm)],[c_1474,c_1477]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_2084,plain,
% 11.17/2.01      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
% 11.17/2.01      inference(global_propositional_subsumption,
% 11.17/2.01                [status(thm)],
% 11.17/2.01                [c_1906,c_32]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_7353,plain,
% 11.17/2.01      ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 11.17/2.01      inference(demodulation,[status(thm)],[c_7345,c_2084]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_7360,plain,
% 11.17/2.01      ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) != sK2
% 11.17/2.01      | sK1 = k1_xboole_0
% 11.17/2.01      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 11.17/2.01      inference(forward_subsumption_resolution,
% 11.17/2.01                [status(thm)],
% 11.17/2.01                [c_7352,c_7353]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_40416,plain,
% 11.17/2.01      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 11.17/2.01      | sK1 = k1_xboole_0
% 11.17/2.01      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 11.17/2.01      inference(superposition,[status(thm)],[c_40059,c_7360]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_40692,plain,
% 11.17/2.01      ( sK1 = k1_xboole_0
% 11.17/2.01      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 11.17/2.01      inference(global_propositional_subsumption,
% 11.17/2.01                [status(thm)],
% 11.17/2.01                [c_40416,c_8797]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_40701,plain,
% 11.17/2.01      ( sK1 = k1_xboole_0
% 11.17/2.01      | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
% 11.17/2.01      | r1_tarski(k1_relat_1(sK3),sK2) != iProver_top ),
% 11.17/2.01      inference(superposition,[status(thm)],[c_4631,c_40692]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_868,plain,( X0 = X0 ),theory(equality) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_1997,plain,
% 11.17/2.01      ( sK2 = sK2 ),
% 11.17/2.01      inference(instantiation,[status(thm)],[c_868]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_5179,plain,
% 11.17/2.01      ( r1_tarski(sK2,sK2) ),
% 11.17/2.01      inference(instantiation,[status(thm)],[c_2]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_870,plain,
% 11.17/2.01      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.17/2.01      theory(equality) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_1784,plain,
% 11.17/2.01      ( ~ r1_tarski(X0,X1)
% 11.17/2.01      | r1_tarski(k1_relat_1(X2),X3)
% 11.17/2.01      | X3 != X1
% 11.17/2.01      | k1_relat_1(X2) != X0 ),
% 11.17/2.01      inference(instantiation,[status(thm)],[c_870]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_2515,plain,
% 11.17/2.01      ( ~ r1_tarski(X0,X1)
% 11.17/2.01      | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X2)
% 11.17/2.01      | X2 != X1
% 11.17/2.01      | k1_relat_1(k7_relat_1(sK3,X0)) != X0 ),
% 11.17/2.01      inference(instantiation,[status(thm)],[c_1784]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_4562,plain,
% 11.17/2.01      ( ~ r1_tarski(X0,X1)
% 11.17/2.01      | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),sK2)
% 11.17/2.01      | k1_relat_1(k7_relat_1(sK3,X0)) != X0
% 11.17/2.01      | sK2 != X1 ),
% 11.17/2.01      inference(instantiation,[status(thm)],[c_2515]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_11047,plain,
% 11.17/2.01      ( ~ r1_tarski(X0,sK2)
% 11.17/2.01      | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),sK2)
% 11.17/2.01      | k1_relat_1(k7_relat_1(sK3,X0)) != X0
% 11.17/2.01      | sK2 != sK2 ),
% 11.17/2.01      inference(instantiation,[status(thm)],[c_4562]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_38982,plain,
% 11.17/2.01      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
% 11.17/2.01      | ~ r1_tarski(sK2,sK2)
% 11.17/2.01      | k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 11.17/2.01      | sK2 != sK2 ),
% 11.17/2.01      inference(instantiation,[status(thm)],[c_11047]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_23,plain,
% 11.17/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.17/2.01      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.17/2.01      | ~ v1_funct_1(X0) ),
% 11.17/2.01      inference(cnf_transformation,[],[f68]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_1478,plain,
% 11.17/2.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.17/2.01      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 11.17/2.01      | v1_funct_1(X0) != iProver_top ),
% 11.17/2.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_7397,plain,
% 11.17/2.01      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 11.17/2.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 11.17/2.01      | v1_funct_1(sK3) != iProver_top ),
% 11.17/2.01      inference(superposition,[status(thm)],[c_7345,c_1478]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_1820,plain,
% 11.17/2.01      ( r1_tarski(k7_relat_1(sK3,X0),sK3) | ~ v1_relat_1(sK3) ),
% 11.17/2.01      inference(instantiation,[status(thm)],[c_11]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_1821,plain,
% 11.17/2.01      ( r1_tarski(k7_relat_1(sK3,X0),sK3) = iProver_top
% 11.17/2.01      | v1_relat_1(sK3) != iProver_top ),
% 11.17/2.01      inference(predicate_to_equality,[status(thm)],[c_1820]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_1774,plain,
% 11.17/2.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 11.17/2.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 11.17/2.01      | ~ r1_tarski(X0,sK3) ),
% 11.17/2.01      inference(instantiation,[status(thm)],[c_16]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_1982,plain,
% 11.17/2.01      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 11.17/2.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 11.17/2.01      | ~ r1_tarski(k7_relat_1(sK3,X0),sK3) ),
% 11.17/2.01      inference(instantiation,[status(thm)],[c_1774]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_1983,plain,
% 11.17/2.01      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 11.17/2.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 11.17/2.01      | r1_tarski(k7_relat_1(sK3,X0),sK3) != iProver_top ),
% 11.17/2.01      inference(predicate_to_equality,[status(thm)],[c_1982]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_7778,plain,
% 11.17/2.01      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 11.17/2.01      inference(global_propositional_subsumption,
% 11.17/2.01                [status(thm)],
% 11.17/2.01                [c_7397,c_34,c_1715,c_1821,c_1983]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_7788,plain,
% 11.17/2.01      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
% 11.17/2.01      | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X1) != iProver_top ),
% 11.17/2.01      inference(superposition,[status(thm)],[c_7778,c_1480]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_40703,plain,
% 11.17/2.01      ( sK1 = k1_xboole_0
% 11.17/2.01      | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) != iProver_top ),
% 11.17/2.01      inference(superposition,[status(thm)],[c_7788,c_40692]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_40725,plain,
% 11.17/2.01      ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
% 11.17/2.01      | sK1 = k1_xboole_0 ),
% 11.17/2.01      inference(predicate_to_equality_rev,[status(thm)],[c_40703]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_40899,plain,
% 11.17/2.01      ( sK1 = k1_xboole_0 ),
% 11.17/2.01      inference(global_propositional_subsumption,
% 11.17/2.01                [status(thm)],
% 11.17/2.01                [c_40701,c_1997,c_5179,c_8797,c_38982,c_40725]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_19,plain,
% 11.17/2.01      ( v1_funct_2(X0,k1_xboole_0,X1)
% 11.17/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 11.17/2.01      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 11.17/2.01      inference(cnf_transformation,[],[f83]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_478,plain,
% 11.17/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 11.17/2.01      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.17/2.01      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 11.17/2.01      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 11.17/2.01      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 11.17/2.01      | sK2 != k1_xboole_0
% 11.17/2.01      | sK1 != X1 ),
% 11.17/2.01      inference(resolution_lifted,[status(thm)],[c_19,c_26]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_479,plain,
% 11.17/2.01      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.17/2.01      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 11.17/2.01      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 11.17/2.01      | k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 11.17/2.01      | sK2 != k1_xboole_0 ),
% 11.17/2.01      inference(unflattening,[status(thm)],[c_478]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_1470,plain,
% 11.17/2.01      ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 11.17/2.01      | sK2 != k1_xboole_0
% 11.17/2.01      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 11.17/2.01      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
% 11.17/2.01      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 11.17/2.01      inference(predicate_to_equality,[status(thm)],[c_479]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_6,plain,
% 11.17/2.01      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 11.17/2.01      inference(cnf_transformation,[],[f79]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_1633,plain,
% 11.17/2.01      ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 11.17/2.01      | sK2 != k1_xboole_0
% 11.17/2.01      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 11.17/2.01      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 11.17/2.01      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 11.17/2.01      inference(demodulation,[status(thm)],[c_1470,c_6]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_2143,plain,
% 11.17/2.01      ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 11.17/2.01      | sK2 != k1_xboole_0
% 11.17/2.01      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 11.17/2.01      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 11.17/2.01      inference(forward_subsumption_resolution,
% 11.17/2.01                [status(thm)],
% 11.17/2.01                [c_1633,c_2084]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_7349,plain,
% 11.17/2.01      ( k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,sK2)) != k1_xboole_0
% 11.17/2.01      | sK2 != k1_xboole_0
% 11.17/2.01      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 11.17/2.01      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 11.17/2.01      inference(demodulation,[status(thm)],[c_7345,c_2143]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_41028,plain,
% 11.17/2.01      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0
% 11.17/2.01      | sK2 != k1_xboole_0
% 11.17/2.01      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
% 11.17/2.01      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 11.17/2.01      inference(demodulation,[status(thm)],[c_40899,c_7349]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_17,plain,
% 11.17/2.01      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 11.17/2.01      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 11.17/2.01      | k1_xboole_0 = X0 ),
% 11.17/2.01      inference(cnf_transformation,[],[f81]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_432,plain,
% 11.17/2.01      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.17/2.01      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 11.17/2.01      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 11.17/2.01      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 11.17/2.01      | sK2 != X0
% 11.17/2.01      | sK1 != k1_xboole_0
% 11.17/2.01      | k1_xboole_0 = X0 ),
% 11.17/2.01      inference(resolution_lifted,[status(thm)],[c_17,c_26]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_433,plain,
% 11.17/2.01      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.17/2.01      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
% 11.17/2.01      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 11.17/2.01      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 11.17/2.01      | sK1 != k1_xboole_0
% 11.17/2.01      | k1_xboole_0 = sK2 ),
% 11.17/2.01      inference(unflattening,[status(thm)],[c_432]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_1472,plain,
% 11.17/2.01      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 11.17/2.01      | sK1 != k1_xboole_0
% 11.17/2.01      | k1_xboole_0 = sK2
% 11.17/2.01      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 11.17/2.01      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
% 11.17/2.01      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 11.17/2.01      inference(predicate_to_equality,[status(thm)],[c_433]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_5,plain,
% 11.17/2.01      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 11.17/2.01      inference(cnf_transformation,[],[f78]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_1620,plain,
% 11.17/2.01      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 11.17/2.01      | sK2 = k1_xboole_0
% 11.17/2.01      | sK1 != k1_xboole_0
% 11.17/2.01      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 11.17/2.01      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 11.17/2.01      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 11.17/2.01      inference(demodulation,[status(thm)],[c_1472,c_5]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_8,plain,
% 11.17/2.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.17/2.01      inference(cnf_transformation,[],[f53]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_84,plain,
% 11.17/2.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 11.17/2.01      | r1_tarski(X0,X1) != iProver_top ),
% 11.17/2.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_86,plain,
% 11.17/2.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 11.17/2.01      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 11.17/2.01      inference(instantiation,[status(thm)],[c_84]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_3,plain,
% 11.17/2.01      ( r1_tarski(k1_xboole_0,X0) ),
% 11.17/2.01      inference(cnf_transformation,[],[f47]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_92,plain,
% 11.17/2.01      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 11.17/2.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_94,plain,
% 11.17/2.01      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 11.17/2.01      inference(instantiation,[status(thm)],[c_92]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_2126,plain,
% 11.17/2.01      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 11.17/2.01      | sK1 != k1_xboole_0
% 11.17/2.01      | sK2 = k1_xboole_0
% 11.17/2.01      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 11.17/2.01      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 11.17/2.01      inference(global_propositional_subsumption,
% 11.17/2.01                [status(thm)],
% 11.17/2.01                [c_1620,c_86,c_94]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_2127,plain,
% 11.17/2.01      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 11.17/2.01      | sK2 = k1_xboole_0
% 11.17/2.01      | sK1 != k1_xboole_0
% 11.17/2.01      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 11.17/2.01      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 11.17/2.01      inference(renaming,[status(thm)],[c_2126]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_2135,plain,
% 11.17/2.01      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 11.17/2.01      | sK2 = k1_xboole_0
% 11.17/2.01      | sK1 != k1_xboole_0
% 11.17/2.01      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 11.17/2.01      inference(forward_subsumption_resolution,
% 11.17/2.01                [status(thm)],
% 11.17/2.01                [c_2127,c_2084]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_7350,plain,
% 11.17/2.01      ( k7_relat_1(sK3,sK2) != k1_xboole_0
% 11.17/2.01      | sK2 = k1_xboole_0
% 11.17/2.01      | sK1 != k1_xboole_0
% 11.17/2.01      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 11.17/2.01      inference(demodulation,[status(thm)],[c_7345,c_2135]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_27,negated_conjecture,
% 11.17/2.01      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 11.17/2.01      inference(cnf_transformation,[],[f74]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_7,plain,
% 11.17/2.01      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 11.17/2.01      | k1_xboole_0 = X0
% 11.17/2.01      | k1_xboole_0 = X1 ),
% 11.17/2.01      inference(cnf_transformation,[],[f49]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_87,plain,
% 11.17/2.01      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 11.17/2.01      | k1_xboole_0 = k1_xboole_0 ),
% 11.17/2.01      inference(instantiation,[status(thm)],[c_7]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_88,plain,
% 11.17/2.01      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 11.17/2.01      inference(instantiation,[status(thm)],[c_6]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_0,plain,
% 11.17/2.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 11.17/2.01      inference(cnf_transformation,[],[f46]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_1730,plain,
% 11.17/2.01      ( ~ r1_tarski(sK2,k1_xboole_0)
% 11.17/2.01      | ~ r1_tarski(k1_xboole_0,sK2)
% 11.17/2.01      | sK2 = k1_xboole_0 ),
% 11.17/2.01      inference(instantiation,[status(thm)],[c_0]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_869,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_2615,plain,
% 11.17/2.01      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 11.17/2.01      inference(instantiation,[status(thm)],[c_869]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_2616,plain,
% 11.17/2.01      ( sK1 != k1_xboole_0
% 11.17/2.01      | k1_xboole_0 = sK1
% 11.17/2.01      | k1_xboole_0 != k1_xboole_0 ),
% 11.17/2.01      inference(instantiation,[status(thm)],[c_2615]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_1936,plain,
% 11.17/2.01      ( ~ r1_tarski(X0,X1)
% 11.17/2.01      | r1_tarski(sK2,k1_xboole_0)
% 11.17/2.01      | sK2 != X0
% 11.17/2.01      | k1_xboole_0 != X1 ),
% 11.17/2.01      inference(instantiation,[status(thm)],[c_870]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_2833,plain,
% 11.17/2.01      ( ~ r1_tarski(sK2,X0)
% 11.17/2.01      | r1_tarski(sK2,k1_xboole_0)
% 11.17/2.01      | sK2 != sK2
% 11.17/2.01      | k1_xboole_0 != X0 ),
% 11.17/2.01      inference(instantiation,[status(thm)],[c_1936]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_5194,plain,
% 11.17/2.01      ( ~ r1_tarski(sK2,sK0)
% 11.17/2.01      | r1_tarski(sK2,k1_xboole_0)
% 11.17/2.01      | sK2 != sK2
% 11.17/2.01      | k1_xboole_0 != sK0 ),
% 11.17/2.01      inference(instantiation,[status(thm)],[c_2833]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_5492,plain,
% 11.17/2.01      ( r1_tarski(k1_xboole_0,sK2) ),
% 11.17/2.01      inference(instantiation,[status(thm)],[c_3]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_8263,plain,
% 11.17/2.01      ( sK1 != k1_xboole_0 | sK2 = k1_xboole_0 ),
% 11.17/2.01      inference(global_propositional_subsumption,
% 11.17/2.01                [status(thm)],
% 11.17/2.01                [c_7350,c_28,c_27,c_87,c_88,c_1730,c_1997,c_2616,c_5194,
% 11.17/2.01                 c_5492]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_8264,plain,
% 11.17/2.01      ( sK2 = k1_xboole_0 | sK1 != k1_xboole_0 ),
% 11.17/2.01      inference(renaming,[status(thm)],[c_8263]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_41029,plain,
% 11.17/2.01      ( sK2 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 11.17/2.01      inference(demodulation,[status(thm)],[c_40899,c_8264]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_41218,plain,
% 11.17/2.01      ( sK2 = k1_xboole_0 ),
% 11.17/2.01      inference(equality_resolution_simp,[status(thm)],[c_41029]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_41228,plain,
% 11.17/2.01      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
% 11.17/2.01      | k1_xboole_0 != k1_xboole_0
% 11.17/2.01      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 11.17/2.01      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 11.17/2.01      inference(light_normalisation,[status(thm)],[c_41028,c_41218]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_41229,plain,
% 11.17/2.01      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
% 11.17/2.01      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 11.17/2.01      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 11.17/2.01      inference(equality_resolution_simp,[status(thm)],[c_41228]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_41031,plain,
% 11.17/2.01      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
% 11.17/2.01      inference(demodulation,[status(thm)],[c_40899,c_7778]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_41060,plain,
% 11.17/2.01      ( sK0 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 11.17/2.01      inference(demodulation,[status(thm)],[c_40899,c_27]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_41061,plain,
% 11.17/2.01      ( sK0 = k1_xboole_0 ),
% 11.17/2.01      inference(equality_resolution_simp,[status(thm)],[c_41060]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_41212,plain,
% 11.17/2.01      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 11.17/2.01      inference(light_normalisation,[status(thm)],[c_41031,c_41061]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_41214,plain,
% 11.17/2.01      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 11.17/2.01      inference(demodulation,[status(thm)],[c_41212,c_6]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_41233,plain,
% 11.17/2.01      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
% 11.17/2.01      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 11.17/2.01      inference(forward_subsumption_resolution,
% 11.17/2.01                [status(thm)],
% 11.17/2.01                [c_41229,c_41214]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_1489,plain,
% 11.17/2.01      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 11.17/2.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_8795,plain,
% 11.17/2.01      ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0
% 11.17/2.01      | sK1 = k1_xboole_0 ),
% 11.17/2.01      inference(superposition,[status(thm)],[c_1489,c_8786]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_1814,plain,
% 11.17/2.01      ( ~ r1_tarski(X0,k1_relat_1(sK3))
% 11.17/2.01      | ~ v1_relat_1(sK3)
% 11.17/2.01      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 11.17/2.01      inference(instantiation,[status(thm)],[c_12]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_1816,plain,
% 11.17/2.01      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK3))
% 11.17/2.01      | ~ v1_relat_1(sK3)
% 11.17/2.01      | k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
% 11.17/2.01      inference(instantiation,[status(thm)],[c_1814]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_2041,plain,
% 11.17/2.01      ( r1_tarski(k1_xboole_0,k1_relat_1(sK3)) ),
% 11.17/2.01      inference(instantiation,[status(thm)],[c_3]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_9273,plain,
% 11.17/2.01      ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
% 11.17/2.01      inference(global_propositional_subsumption,
% 11.17/2.01                [status(thm)],
% 11.17/2.01                [c_8795,c_29,c_1714,c_1816,c_2041]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_12851,plain,
% 11.17/2.01      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 11.17/2.01      | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_xboole_0) != iProver_top ),
% 11.17/2.01      inference(superposition,[status(thm)],[c_6,c_7788]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_13192,plain,
% 11.17/2.01      ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 11.17/2.01      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 11.17/2.01      inference(superposition,[status(thm)],[c_9273,c_12851]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_1823,plain,
% 11.17/2.01      ( r1_tarski(k7_relat_1(sK3,k1_xboole_0),sK3) = iProver_top
% 11.17/2.01      | v1_relat_1(sK3) != iProver_top ),
% 11.17/2.01      inference(instantiation,[status(thm)],[c_1821]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_6179,plain,
% 11.17/2.01      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 11.17/2.01      | r1_tarski(X0,sK3) != iProver_top
% 11.17/2.01      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top ),
% 11.17/2.01      inference(superposition,[status(thm)],[c_6,c_4102]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_9276,plain,
% 11.17/2.01      ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 11.17/2.01      | r1_tarski(k7_relat_1(sK3,k1_xboole_0),sK3) != iProver_top
% 11.17/2.01      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 11.17/2.01      inference(superposition,[status(thm)],[c_9273,c_6179]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_19714,plain,
% 11.17/2.01      ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 11.17/2.01      inference(global_propositional_subsumption,
% 11.17/2.01                [status(thm)],
% 11.17/2.01                [c_13192,c_34,c_94,c_1715,c_1823,c_9276]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_9,plain,
% 11.17/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 11.17/2.01      inference(cnf_transformation,[],[f52]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_1486,plain,
% 11.17/2.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.17/2.01      | r1_tarski(X0,X1) = iProver_top ),
% 11.17/2.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_19719,plain,
% 11.17/2.01      ( r1_tarski(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 11.17/2.01      inference(superposition,[status(thm)],[c_19714,c_1486]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_4,plain,
% 11.17/2.01      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 11.17/2.01      inference(cnf_transformation,[],[f48]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_1488,plain,
% 11.17/2.01      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 11.17/2.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_19821,plain,
% 11.17/2.01      ( k7_relat_1(sK3,k1_xboole_0) = k1_xboole_0 ),
% 11.17/2.01      inference(superposition,[status(thm)],[c_19719,c_1488]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_41234,plain,
% 11.17/2.01      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 11.17/2.01      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 11.17/2.01      inference(light_normalisation,[status(thm)],[c_41233,c_19821]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_1487,plain,
% 11.17/2.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 11.17/2.01      | r1_tarski(X0,X1) != iProver_top ),
% 11.17/2.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_3057,plain,
% 11.17/2.01      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
% 11.17/2.01      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 11.17/2.01      inference(superposition,[status(thm)],[c_6,c_1481]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_3194,plain,
% 11.17/2.01      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
% 11.17/2.01      | r1_tarski(X1,k1_xboole_0) != iProver_top ),
% 11.17/2.01      inference(superposition,[status(thm)],[c_1487,c_3057]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_12502,plain,
% 11.17/2.01      ( k1_relset_1(k1_xboole_0,X0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 11.17/2.01      inference(superposition,[status(thm)],[c_1490,c_3194]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_41235,plain,
% 11.17/2.01      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 11.17/2.01      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 11.17/2.01      inference(demodulation,[status(thm)],[c_41234,c_6,c_12502]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_10,plain,
% 11.17/2.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 11.17/2.01      inference(cnf_transformation,[],[f54]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_1485,plain,
% 11.17/2.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 11.17/2.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_2415,plain,
% 11.17/2.01      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 11.17/2.01      inference(superposition,[status(thm)],[c_5,c_1485]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_4248,plain,
% 11.17/2.01      ( k1_relat_1(k7_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 11.17/2.01      | v1_relat_1(X0) != iProver_top ),
% 11.17/2.01      inference(superposition,[status(thm)],[c_1489,c_1483]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_10901,plain,
% 11.17/2.01      ( k1_relat_1(k7_relat_1(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
% 11.17/2.01      inference(superposition,[status(thm)],[c_2415,c_4248]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_2586,plain,
% 11.17/2.01      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
% 11.17/2.01      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 11.17/2.01      inference(superposition,[status(thm)],[c_1484,c_1488]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_1775,plain,
% 11.17/2.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 11.17/2.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 11.17/2.01      | r1_tarski(X0,sK3) != iProver_top ),
% 11.17/2.01      inference(predicate_to_equality,[status(thm)],[c_1774]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_1777,plain,
% 11.17/2.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 11.17/2.01      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 11.17/2.01      | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 11.17/2.01      inference(instantiation,[status(thm)],[c_1775]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_1846,plain,
% 11.17/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 11.17/2.01      | v1_relat_1(X0) ),
% 11.17/2.01      inference(instantiation,[status(thm)],[c_13]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_1847,plain,
% 11.17/2.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 11.17/2.01      | v1_relat_1(X0) = iProver_top ),
% 11.17/2.01      inference(predicate_to_equality,[status(thm)],[c_1846]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_1849,plain,
% 11.17/2.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 11.17/2.01      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 11.17/2.01      inference(instantiation,[status(thm)],[c_1847]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_1966,plain,
% 11.17/2.01      ( r1_tarski(k1_xboole_0,sK3) ),
% 11.17/2.01      inference(instantiation,[status(thm)],[c_3]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_1969,plain,
% 11.17/2.01      ( r1_tarski(k1_xboole_0,sK3) = iProver_top ),
% 11.17/2.01      inference(predicate_to_equality,[status(thm)],[c_1966]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_2739,plain,
% 11.17/2.01      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 11.17/2.01      inference(global_propositional_subsumption,
% 11.17/2.01                [status(thm)],
% 11.17/2.01                [c_2586,c_34,c_1777,c_1849,c_1969]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(c_10907,plain,
% 11.17/2.01      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 11.17/2.01      inference(demodulation,[status(thm)],[c_10901,c_2739]) ).
% 11.17/2.01  
% 11.17/2.01  cnf(contradiction,plain,
% 11.17/2.01      ( $false ),
% 11.17/2.01      inference(minisat,[status(thm)],[c_41235,c_10907,c_94,c_86]) ).
% 11.17/2.01  
% 11.17/2.01  
% 11.17/2.01  % SZS output end CNFRefutation for theBenchmark.p
% 11.17/2.01  
% 11.17/2.01  ------                               Statistics
% 11.17/2.01  
% 11.17/2.01  ------ General
% 11.17/2.01  
% 11.17/2.01  abstr_ref_over_cycles:                  0
% 11.17/2.01  abstr_ref_under_cycles:                 0
% 11.17/2.01  gc_basic_clause_elim:                   0
% 11.17/2.01  forced_gc_time:                         0
% 11.17/2.01  parsing_time:                           0.016
% 11.17/2.01  unif_index_cands_time:                  0.
% 11.17/2.01  unif_index_add_time:                    0.
% 11.17/2.01  orderings_time:                         0.
% 11.17/2.01  out_proof_time:                         0.021
% 11.17/2.01  total_time:                             1.038
% 11.17/2.01  num_of_symbols:                         47
% 11.17/2.01  num_of_terms:                           31692
% 11.17/2.01  
% 11.17/2.01  ------ Preprocessing
% 11.17/2.01  
% 11.17/2.01  num_of_splits:                          0
% 11.17/2.01  num_of_split_atoms:                     0
% 11.17/2.01  num_of_reused_defs:                     0
% 11.17/2.01  num_eq_ax_congr_red:                    8
% 11.17/2.01  num_of_sem_filtered_clauses:            1
% 11.17/2.01  num_of_subtypes:                        0
% 11.17/2.01  monotx_restored_types:                  0
% 11.17/2.01  sat_num_of_epr_types:                   0
% 11.17/2.01  sat_num_of_non_cyclic_types:            0
% 11.17/2.01  sat_guarded_non_collapsed_types:        0
% 11.17/2.01  num_pure_diseq_elim:                    0
% 11.17/2.01  simp_replaced_by:                       0
% 11.17/2.01  res_preprocessed:                       144
% 11.17/2.01  prep_upred:                             0
% 11.17/2.01  prep_unflattend:                        39
% 11.17/2.01  smt_new_axioms:                         0
% 11.17/2.01  pred_elim_cands:                        4
% 11.17/2.01  pred_elim:                              1
% 11.17/2.01  pred_elim_cl:                           1
% 11.17/2.01  pred_elim_cycles:                       4
% 11.17/2.01  merged_defs:                            8
% 11.17/2.01  merged_defs_ncl:                        0
% 11.17/2.01  bin_hyper_res:                          8
% 11.17/2.01  prep_cycles:                            4
% 11.17/2.01  pred_elim_time:                         0.007
% 11.17/2.01  splitting_time:                         0.
% 11.17/2.01  sem_filter_time:                        0.
% 11.17/2.01  monotx_time:                            0.
% 11.17/2.01  subtype_inf_time:                       0.
% 11.17/2.01  
% 11.17/2.01  ------ Problem properties
% 11.17/2.01  
% 11.17/2.01  clauses:                                30
% 11.17/2.01  conjectures:                            4
% 11.17/2.01  epr:                                    7
% 11.17/2.01  horn:                                   27
% 11.17/2.01  ground:                                 11
% 11.17/2.01  unary:                                  8
% 11.17/2.01  binary:                                 8
% 11.17/2.01  lits:                                   74
% 11.17/2.01  lits_eq:                                28
% 11.17/2.01  fd_pure:                                0
% 11.17/2.01  fd_pseudo:                              0
% 11.17/2.01  fd_cond:                                2
% 11.17/2.01  fd_pseudo_cond:                         1
% 11.17/2.01  ac_symbols:                             0
% 11.17/2.01  
% 11.17/2.01  ------ Propositional Solver
% 11.17/2.01  
% 11.17/2.01  prop_solver_calls:                      30
% 11.17/2.01  prop_fast_solver_calls:                 1782
% 11.17/2.01  smt_solver_calls:                       0
% 11.17/2.01  smt_fast_solver_calls:                  0
% 11.17/2.01  prop_num_of_clauses:                    15498
% 11.17/2.01  prop_preprocess_simplified:             28714
% 11.17/2.01  prop_fo_subsumed:                       57
% 11.17/2.01  prop_solver_time:                       0.
% 11.17/2.01  smt_solver_time:                        0.
% 11.17/2.01  smt_fast_solver_time:                   0.
% 11.17/2.01  prop_fast_solver_time:                  0.
% 11.17/2.01  prop_unsat_core_time:                   0.001
% 11.17/2.01  
% 11.17/2.01  ------ QBF
% 11.17/2.01  
% 11.17/2.01  qbf_q_res:                              0
% 11.17/2.01  qbf_num_tautologies:                    0
% 11.17/2.01  qbf_prep_cycles:                        0
% 11.17/2.01  
% 11.17/2.01  ------ BMC1
% 11.17/2.01  
% 11.17/2.01  bmc1_current_bound:                     -1
% 11.17/2.01  bmc1_last_solved_bound:                 -1
% 11.17/2.01  bmc1_unsat_core_size:                   -1
% 11.17/2.01  bmc1_unsat_core_parents_size:           -1
% 11.17/2.01  bmc1_merge_next_fun:                    0
% 11.17/2.01  bmc1_unsat_core_clauses_time:           0.
% 11.17/2.01  
% 11.17/2.01  ------ Instantiation
% 11.17/2.01  
% 11.17/2.01  inst_num_of_clauses:                    4394
% 11.17/2.01  inst_num_in_passive:                    1348
% 11.17/2.01  inst_num_in_active:                     1528
% 11.17/2.01  inst_num_in_unprocessed:                1520
% 11.17/2.01  inst_num_of_loops:                      1730
% 11.17/2.01  inst_num_of_learning_restarts:          0
% 11.17/2.01  inst_num_moves_active_passive:          200
% 11.17/2.01  inst_lit_activity:                      0
% 11.17/2.01  inst_lit_activity_moves:                0
% 11.17/2.01  inst_num_tautologies:                   0
% 11.17/2.01  inst_num_prop_implied:                  0
% 11.17/2.01  inst_num_existing_simplified:           0
% 11.17/2.01  inst_num_eq_res_simplified:             0
% 11.17/2.01  inst_num_child_elim:                    0
% 11.17/2.01  inst_num_of_dismatching_blockings:      3016
% 11.17/2.01  inst_num_of_non_proper_insts:           5730
% 11.17/2.01  inst_num_of_duplicates:                 0
% 11.17/2.01  inst_inst_num_from_inst_to_res:         0
% 11.17/2.01  inst_dismatching_checking_time:         0.
% 11.17/2.01  
% 11.17/2.01  ------ Resolution
% 11.17/2.01  
% 11.17/2.01  res_num_of_clauses:                     0
% 11.17/2.01  res_num_in_passive:                     0
% 11.17/2.01  res_num_in_active:                      0
% 11.17/2.01  res_num_of_loops:                       148
% 11.17/2.01  res_forward_subset_subsumed:            176
% 11.17/2.01  res_backward_subset_subsumed:           4
% 11.17/2.01  res_forward_subsumed:                   0
% 11.17/2.01  res_backward_subsumed:                  0
% 11.17/2.01  res_forward_subsumption_resolution:     0
% 11.17/2.01  res_backward_subsumption_resolution:    0
% 11.17/2.01  res_clause_to_clause_subsumption:       5140
% 11.17/2.01  res_orphan_elimination:                 0
% 11.17/2.01  res_tautology_del:                      299
% 11.17/2.01  res_num_eq_res_simplified:              1
% 11.17/2.01  res_num_sel_changes:                    0
% 11.17/2.01  res_moves_from_active_to_pass:          0
% 11.17/2.01  
% 11.17/2.01  ------ Superposition
% 11.17/2.01  
% 11.17/2.01  sup_time_total:                         0.
% 11.17/2.01  sup_time_generating:                    0.
% 11.17/2.01  sup_time_sim_full:                      0.
% 11.17/2.01  sup_time_sim_immed:                     0.
% 11.17/2.01  
% 11.17/2.01  sup_num_of_clauses:                     596
% 11.17/2.01  sup_num_in_active:                      149
% 11.17/2.01  sup_num_in_passive:                     447
% 11.17/2.01  sup_num_of_loops:                       344
% 11.17/2.01  sup_fw_superposition:                   666
% 11.17/2.01  sup_bw_superposition:                   609
% 11.17/2.01  sup_immediate_simplified:               478
% 11.17/2.01  sup_given_eliminated:                   1
% 11.17/2.01  comparisons_done:                       0
% 11.17/2.01  comparisons_avoided:                    114
% 11.17/2.01  
% 11.17/2.01  ------ Simplifications
% 11.17/2.01  
% 11.17/2.01  
% 11.17/2.01  sim_fw_subset_subsumed:                 128
% 11.17/2.01  sim_bw_subset_subsumed:                 77
% 11.17/2.01  sim_fw_subsumed:                        142
% 11.17/2.01  sim_bw_subsumed:                        15
% 11.17/2.01  sim_fw_subsumption_res:                 8
% 11.17/2.01  sim_bw_subsumption_res:                 0
% 11.17/2.01  sim_tautology_del:                      9
% 11.17/2.01  sim_eq_tautology_del:                   60
% 11.17/2.01  sim_eq_res_simp:                        5
% 11.17/2.01  sim_fw_demodulated:                     87
% 11.17/2.01  sim_bw_demodulated:                     177
% 11.17/2.01  sim_light_normalised:                   195
% 11.17/2.01  sim_joinable_taut:                      0
% 11.17/2.01  sim_joinable_simp:                      0
% 11.17/2.01  sim_ac_normalised:                      0
% 11.17/2.01  sim_smt_subsumption:                    0
% 11.17/2.01  
%------------------------------------------------------------------------------
