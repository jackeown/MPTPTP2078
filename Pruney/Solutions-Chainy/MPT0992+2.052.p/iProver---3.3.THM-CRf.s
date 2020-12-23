%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:56 EST 2020

% Result     : Theorem 6.68s
% Output     : CNFRefutation 6.68s
% Verified   : 
% Statistics : Number of formulae       :  250 (2034 expanded)
%              Number of clauses        :  170 ( 702 expanded)
%              Number of leaves         :   25 ( 386 expanded)
%              Depth                    :   24
%              Number of atoms          :  742 (11238 expanded)
%              Number of equality atoms :  364 (3162 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
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

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f20])).

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
    inference(flattening,[],[f39])).

fof(f51,plain,
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
   => ( ( ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
        | ~ v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK3,sK2)
        | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3)) )
      & ( k1_xboole_0 = sK1
        | k1_xboole_0 != sK2 )
      & r1_tarski(sK3,sK1)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK4,sK1,sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
      | ~ v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK3,sK2)
      | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3)) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 != sK2 )
    & r1_tarski(sK3,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f40,f51])).

fof(f88,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f52])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f86,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f52])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f89,plain,(
    r1_tarski(sK3,sK1) ),
    inference(cnf_transformation,[],[f52])).

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
    inference(ennf_transformation,[],[f15])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

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
    inference(nnf_transformation,[],[f32])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f87,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f91,plain,
    ( ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK3,sK2)
    | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3)) ),
    inference(cnf_transformation,[],[f52])).

fof(f90,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f52])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f47])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f95,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f62])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f45])).

fof(f59,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f41])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f93,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1835,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1838,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4437,plain,
    ( k2_partfun1(sK1,sK2,sK4,X0) = k7_relat_1(sK4,X0)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1835,c_1838])).

cnf(c_38,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2232,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_2361,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(sK1,sK2,sK4,X0) = k7_relat_1(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_2232])).

cnf(c_4820,plain,
    ( k2_partfun1(sK1,sK2,sK4,X0) = k7_relat_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4437,c_38,c_36,c_2361])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1840,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_6474,plain,
    ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4820,c_1840])).

cnf(c_39,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_41,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_6906,plain,
    ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6474,c_39,c_41])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1841,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_6918,plain,
    ( k2_relset_1(sK1,sK2,k7_relat_1(sK4,X0)) = k2_relat_1(k7_relat_1(sK4,X0)) ),
    inference(superposition,[status(thm)],[c_6906,c_1841])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1843,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_7200,plain,
    ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(k2_relat_1(k7_relat_1(sK4,X0)),k1_zfmisc_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6918,c_1843])).

cnf(c_9882,plain,
    ( m1_subset_1(k2_relat_1(k7_relat_1(sK4,X0)),k1_zfmisc_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7200,c_39,c_41,c_6474])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1848,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_9889,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK4,X0)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_9882,c_1848])).

cnf(c_35,negated_conjecture,
    ( r1_tarski(sK3,sK1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1836,plain,
    ( r1_tarski(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_37,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_650,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X0
    | sK2 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_37])).

cnf(c_651,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_650])).

cnf(c_653,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_651,c_36])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1842,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3767,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1835,c_1842])).

cnf(c_4086,plain,
    ( k1_relat_1(sK4) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_653,c_3767])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1845,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_5547,plain,
    ( k1_relat_1(k7_relat_1(sK4,X0)) = X0
    | sK2 = k1_xboole_0
    | r1_tarski(X0,sK1) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4086,c_1845])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2153,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2154,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2153])).

cnf(c_5714,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | sK2 = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK4,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5547,c_41,c_2154])).

cnf(c_5715,plain,
    ( k1_relat_1(k7_relat_1(sK4,X0)) = X0
    | sK2 = k1_xboole_0
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5714])).

cnf(c_5726,plain,
    ( k1_relat_1(k7_relat_1(sK4,sK3)) = sK3
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1836,c_5715])).

cnf(c_30,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1837,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_5809,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK3)),X0) != iProver_top
    | v1_funct_1(k7_relat_1(sK4,sK3)) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5726,c_1837])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1839,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_5194,plain,
    ( v1_funct_1(k2_partfun1(sK1,sK2,sK4,X0)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1835,c_1839])).

cnf(c_5220,plain,
    ( v1_funct_1(k7_relat_1(sK4,X0)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5194,c_4820])).

cnf(c_5706,plain,
    ( v1_funct_1(k7_relat_1(sK4,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5220,c_39])).

cnf(c_5984,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK3)),X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK3)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5809,c_5706])).

cnf(c_31,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_33,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK3,sK2)
    | ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_661,plain,
    ( ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))
    | ~ v1_relat_1(X0)
    | k2_partfun1(sK1,sK2,sK4,sK3) != X0
    | k1_relat_1(X0) != sK3
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_33])).

cnf(c_662,plain,
    ( ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ r1_tarski(k2_relat_1(k2_partfun1(sK1,sK2,sK4,sK3)),sK2)
    | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))
    | ~ v1_relat_1(k2_partfun1(sK1,sK2,sK4,sK3))
    | k1_relat_1(k2_partfun1(sK1,sK2,sK4,sK3)) != sK3 ),
    inference(unflattening,[status(thm)],[c_661])).

cnf(c_674,plain,
    ( ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ r1_tarski(k2_relat_1(k2_partfun1(sK1,sK2,sK4,sK3)),sK2)
    | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))
    | k1_relat_1(k2_partfun1(sK1,sK2,sK4,sK3)) != sK3 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_662,c_17])).

cnf(c_1824,plain,
    ( k1_relat_1(k2_partfun1(sK1,sK2,sK4,sK3)) != sK3
    | m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | r1_tarski(k2_relat_1(k2_partfun1(sK1,sK2,sK4,sK3)),sK2) != iProver_top
    | v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_674])).

cnf(c_4826,plain,
    ( k1_relat_1(k7_relat_1(sK4,sK3)) != sK3
    | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK3)),sK2) != iProver_top
    | v1_funct_1(k7_relat_1(sK4,sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4820,c_1824])).

cnf(c_5810,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK3)),sK2) != iProver_top
    | v1_funct_1(k7_relat_1(sK4,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5726,c_4826])).

cnf(c_5849,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK3)),sK2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5810,c_5706])).

cnf(c_5995,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK3)),sK2) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5984,c_5849])).

cnf(c_1844,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_6915,plain,
    ( v1_relat_1(k7_relat_1(sK4,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6906,c_1844])).

cnf(c_9472,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK3)),sK2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5995,c_6915])).

cnf(c_20925,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9889,c_9472])).

cnf(c_21164,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_20925,c_1835])).

cnf(c_34,negated_conjecture,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_21165,plain,
    ( sK1 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_20925,c_34])).

cnf(c_21166,plain,
    ( sK1 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_21165])).

cnf(c_21169,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_21164,c_21166])).

cnf(c_9,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_21171,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_21169,c_9])).

cnf(c_1066,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | k2_partfun1(X0,X2,X4,X6) = k2_partfun1(X1,X3,X5,X7) ),
    theory(equality)).

cnf(c_3045,plain,
    ( X0 != X1
    | X2 != sK4
    | X3 != sK2
    | X4 != sK1
    | k2_partfun1(X4,X3,X2,X0) = k2_partfun1(sK1,sK2,sK4,X1) ),
    inference(instantiation,[status(thm)],[c_1066])).

cnf(c_7787,plain,
    ( X0 != X1
    | X2 != sK4
    | X3 != sK1
    | k2_partfun1(X3,sK2,X2,X0) = k2_partfun1(sK1,sK2,sK4,X1)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_3045])).

cnf(c_16896,plain,
    ( k2_partfun1(sK1,sK2,sK4,sK3) = k2_partfun1(sK1,sK2,sK4,X0)
    | sK3 != X0
    | sK4 != sK4
    | sK2 != sK2
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_7787])).

cnf(c_16901,plain,
    ( k2_partfun1(sK1,sK2,sK4,sK3) = k2_partfun1(sK1,sK2,sK4,k1_xboole_0)
    | sK3 != k1_xboole_0
    | sK4 != sK4
    | sK2 != sK2
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_16896])).

cnf(c_1057,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2722,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK1,sK3)
    | sK3 != X1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_1057])).

cnf(c_14621,plain,
    ( ~ r1_tarski(X0,sK3)
    | r1_tarski(sK1,sK3)
    | sK3 != sK3
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_2722])).

cnf(c_14623,plain,
    ( r1_tarski(sK1,sK3)
    | ~ r1_tarski(k1_xboole_0,sK3)
    | sK3 != sK3
    | sK1 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_14621])).

cnf(c_2395,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK3,k1_xboole_0)
    | sK3 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_1057])).

cnf(c_6686,plain,
    ( ~ r1_tarski(sK3,X0)
    | r1_tarski(sK3,k1_xboole_0)
    | sK3 != sK3
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_2395])).

cnf(c_13331,plain,
    ( ~ r1_tarski(sK3,sK1)
    | r1_tarski(sK3,k1_xboole_0)
    | sK3 != sK3
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_6686])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_11,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_271,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_11])).

cnf(c_272,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_271])).

cnf(c_337,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_13,c_272])).

cnf(c_454,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_337])).

cnf(c_455,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_454])).

cnf(c_12317,plain,
    ( ~ r2_hidden(sK0(sK4,k7_relat_1(sK4,X0)),sK4)
    | ~ r1_tarski(sK4,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_455])).

cnf(c_12318,plain,
    ( r2_hidden(sK0(sK4,k7_relat_1(sK4,X0)),sK4) != iProver_top
    | r1_tarski(sK4,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12317])).

cnf(c_12320,plain,
    ( r2_hidden(sK0(sK4,k7_relat_1(sK4,k1_xboole_0)),sK4) != iProver_top
    | r1_tarski(sK4,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_12318])).

cnf(c_1056,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3042,plain,
    ( X0 != X1
    | X0 = k2_partfun1(sK1,sK2,sK4,X2)
    | k2_partfun1(sK1,sK2,sK4,X2) != X1 ),
    inference(instantiation,[status(thm)],[c_1056])).

cnf(c_7294,plain,
    ( X0 = k2_partfun1(sK1,sK2,sK4,X1)
    | X0 != k7_relat_1(sK4,X1)
    | k2_partfun1(sK1,sK2,sK4,X1) != k7_relat_1(sK4,X1) ),
    inference(instantiation,[status(thm)],[c_3042])).

cnf(c_10118,plain,
    ( k2_partfun1(sK1,sK2,sK4,X0) != k7_relat_1(sK4,X0)
    | sK4 = k2_partfun1(sK1,sK2,sK4,X0)
    | sK4 != k7_relat_1(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_7294])).

cnf(c_10119,plain,
    ( k2_partfun1(sK1,sK2,sK4,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0)
    | sK4 = k2_partfun1(sK1,sK2,sK4,k1_xboole_0)
    | sK4 != k7_relat_1(sK4,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_10118])).

cnf(c_7,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2307,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_9443,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_2307])).

cnf(c_2279,plain,
    ( X0 != X1
    | X0 = sK4
    | sK4 != X1 ),
    inference(instantiation,[status(thm)],[c_1056])).

cnf(c_4758,plain,
    ( k2_partfun1(sK1,sK2,sK4,sK3) != X0
    | k2_partfun1(sK1,sK2,sK4,sK3) = sK4
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_2279])).

cnf(c_8937,plain,
    ( k2_partfun1(sK1,sK2,sK4,sK3) != k2_partfun1(sK1,sK2,sK4,X0)
    | k2_partfun1(sK1,sK2,sK4,sK3) = sK4
    | sK4 != k2_partfun1(sK1,sK2,sK4,X0) ),
    inference(instantiation,[status(thm)],[c_4758])).

cnf(c_8940,plain,
    ( k2_partfun1(sK1,sK2,sK4,sK3) != k2_partfun1(sK1,sK2,sK4,k1_xboole_0)
    | k2_partfun1(sK1,sK2,sK4,sK3) = sK4
    | sK4 != k2_partfun1(sK1,sK2,sK4,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_8937])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2689,plain,
    ( ~ r1_tarski(X0,sK4)
    | ~ r1_tarski(sK4,X0)
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_8807,plain,
    ( ~ r1_tarski(k7_relat_1(sK4,X0),sK4)
    | ~ r1_tarski(sK4,k7_relat_1(sK4,X0))
    | sK4 = k7_relat_1(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_2689])).

cnf(c_8808,plain,
    ( sK4 = k7_relat_1(sK4,X0)
    | r1_tarski(k7_relat_1(sK4,X0),sK4) != iProver_top
    | r1_tarski(sK4,k7_relat_1(sK4,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8807])).

cnf(c_8810,plain,
    ( sK4 = k7_relat_1(sK4,k1_xboole_0)
    | r1_tarski(k7_relat_1(sK4,k1_xboole_0),sK4) != iProver_top
    | r1_tarski(sK4,k7_relat_1(sK4,k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8808])).

cnf(c_7778,plain,
    ( X0 != X1
    | X0 = sK2
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_1056])).

cnf(c_7779,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7778])).

cnf(c_1061,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2221,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | X0 != X2
    | X1 != k1_zfmisc_1(X3) ),
    inference(instantiation,[status(thm)],[c_1061])).

cnf(c_2868,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(X1))
    | X2 != X0
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_2221])).

cnf(c_3949,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_2868])).

cnf(c_5291,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_3949])).

cnf(c_5295,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5291])).

cnf(c_3930,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | k2_partfun1(sK1,sK2,sK4,sK3) != X0
    | k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_2868])).

cnf(c_5290,plain,
    ( m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | k2_partfun1(sK1,sK2,sK4,sK3) != sK4
    | k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_3930])).

cnf(c_2148,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_5265,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ r1_tarski(X0,k2_zfmisc_1(sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_2148])).

cnf(c_5267,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_5265])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_3329,plain,
    ( r2_hidden(sK0(sK4,X0),sK4)
    | r1_tarski(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_4718,plain,
    ( r2_hidden(sK0(sK4,k7_relat_1(sK4,X0)),sK4)
    | r1_tarski(sK4,k7_relat_1(sK4,X0)) ),
    inference(instantiation,[status(thm)],[c_3329])).

cnf(c_4719,plain,
    ( r2_hidden(sK0(sK4,k7_relat_1(sK4,X0)),sK4) = iProver_top
    | r1_tarski(sK4,k7_relat_1(sK4,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4718])).

cnf(c_4721,plain,
    ( r2_hidden(sK0(sK4,k7_relat_1(sK4,k1_xboole_0)),sK4) = iProver_top
    | r1_tarski(sK4,k7_relat_1(sK4,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4719])).

cnf(c_1055,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2869,plain,
    ( k1_zfmisc_1(X0) = k1_zfmisc_1(X0) ),
    inference(instantiation,[status(thm)],[c_1055])).

cnf(c_4255,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)) = k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_2869])).

cnf(c_1852,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3887,plain,
    ( sK3 = sK1
    | r1_tarski(sK1,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1836,c_1852])).

cnf(c_3916,plain,
    ( ~ r1_tarski(sK1,sK3)
    | sK3 = sK1 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3887])).

cnf(c_3330,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
    | r1_tarski(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_3331,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3330])).

cnf(c_3333,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK4,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3331])).

cnf(c_2749,plain,
    ( r1_tarski(k1_xboole_0,sK3) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2690,plain,
    ( sK4 = X0
    | r1_tarski(X0,sK4) != iProver_top
    | r1_tarski(sK4,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2689])).

cnf(c_2692,plain,
    ( sK4 = k1_xboole_0
    | r1_tarski(sK4,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2690])).

cnf(c_2661,plain,
    ( r1_tarski(k1_xboole_0,sK4) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2664,plain,
    ( r1_tarski(k1_xboole_0,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2661])).

cnf(c_6,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2655,plain,
    ( r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2263,plain,
    ( ~ r1_tarski(X0,sK4)
    | ~ r1_tarski(sK4,X0)
    | X0 = sK4 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2654,plain,
    ( ~ r1_tarski(sK4,sK4)
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_2263])).

cnf(c_2561,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1055])).

cnf(c_2182,plain,
    ( sK1 != X0
    | sK1 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1056])).

cnf(c_2560,plain,
    ( sK1 != sK1
    | sK1 = k1_xboole_0
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_2182])).

cnf(c_2555,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1055])).

cnf(c_2549,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1055])).

cnf(c_2211,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_partfun1(X0,X1,sK4,X2))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_2355,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_funct_1(k2_partfun1(sK1,sK2,sK4,X0))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2211])).

cnf(c_2463,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2355])).

cnf(c_2363,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(sK1,sK2,sK4,k1_xboole_0) = k7_relat_1(sK4,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2361])).

cnf(c_15,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2245,plain,
    ( r1_tarski(k7_relat_1(sK4,X0),sK4)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2246,plain,
    ( r1_tarski(k7_relat_1(sK4,X0),sK4) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2245])).

cnf(c_2248,plain,
    ( r1_tarski(k7_relat_1(sK4,k1_xboole_0),sK4) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2246])).

cnf(c_2171,plain,
    ( ~ r1_tarski(sK3,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK3)
    | sK3 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_680,plain,
    ( ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))
    | k2_partfun1(sK1,sK2,sK4,sK3) != sK4
    | sK3 != sK1
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_37])).

cnf(c_109,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_10,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_108,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_21171,c_20925,c_16901,c_14623,c_13331,c_12320,c_10119,c_9443,c_8940,c_8810,c_7779,c_5295,c_5290,c_5267,c_4721,c_4255,c_3916,c_3333,c_2749,c_2692,c_2664,c_2655,c_2654,c_2561,c_2560,c_2555,c_2549,c_2463,c_2363,c_2248,c_2171,c_2154,c_680,c_109,c_108,c_34,c_35,c_41,c_36,c_38])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:28:39 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 6.68/1.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.68/1.51  
% 6.68/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.68/1.51  
% 6.68/1.51  ------  iProver source info
% 6.68/1.51  
% 6.68/1.51  git: date: 2020-06-30 10:37:57 +0100
% 6.68/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.68/1.51  git: non_committed_changes: false
% 6.68/1.51  git: last_make_outside_of_git: false
% 6.68/1.51  
% 6.68/1.51  ------ 
% 6.68/1.51  
% 6.68/1.51  ------ Input Options
% 6.68/1.51  
% 6.68/1.51  --out_options                           all
% 6.68/1.51  --tptp_safe_out                         true
% 6.68/1.51  --problem_path                          ""
% 6.68/1.51  --include_path                          ""
% 6.68/1.51  --clausifier                            res/vclausify_rel
% 6.68/1.51  --clausifier_options                    --mode clausify
% 6.68/1.51  --stdin                                 false
% 6.68/1.51  --stats_out                             all
% 6.68/1.51  
% 6.68/1.51  ------ General Options
% 6.68/1.51  
% 6.68/1.51  --fof                                   false
% 6.68/1.51  --time_out_real                         305.
% 6.68/1.51  --time_out_virtual                      -1.
% 6.68/1.51  --symbol_type_check                     false
% 6.68/1.51  --clausify_out                          false
% 6.68/1.51  --sig_cnt_out                           false
% 6.68/1.51  --trig_cnt_out                          false
% 6.68/1.51  --trig_cnt_out_tolerance                1.
% 6.68/1.51  --trig_cnt_out_sk_spl                   false
% 6.68/1.51  --abstr_cl_out                          false
% 6.68/1.51  
% 6.68/1.51  ------ Global Options
% 6.68/1.51  
% 6.68/1.51  --schedule                              default
% 6.68/1.51  --add_important_lit                     false
% 6.68/1.51  --prop_solver_per_cl                    1000
% 6.68/1.51  --min_unsat_core                        false
% 6.68/1.51  --soft_assumptions                      false
% 6.68/1.51  --soft_lemma_size                       3
% 6.68/1.51  --prop_impl_unit_size                   0
% 6.68/1.51  --prop_impl_unit                        []
% 6.68/1.51  --share_sel_clauses                     true
% 6.68/1.51  --reset_solvers                         false
% 6.68/1.51  --bc_imp_inh                            [conj_cone]
% 6.68/1.51  --conj_cone_tolerance                   3.
% 6.68/1.51  --extra_neg_conj                        none
% 6.68/1.51  --large_theory_mode                     true
% 6.68/1.51  --prolific_symb_bound                   200
% 6.68/1.51  --lt_threshold                          2000
% 6.68/1.51  --clause_weak_htbl                      true
% 6.68/1.51  --gc_record_bc_elim                     false
% 6.68/1.51  
% 6.68/1.51  ------ Preprocessing Options
% 6.68/1.51  
% 6.68/1.51  --preprocessing_flag                    true
% 6.68/1.51  --time_out_prep_mult                    0.1
% 6.68/1.51  --splitting_mode                        input
% 6.68/1.51  --splitting_grd                         true
% 6.68/1.51  --splitting_cvd                         false
% 6.68/1.51  --splitting_cvd_svl                     false
% 6.68/1.51  --splitting_nvd                         32
% 6.68/1.51  --sub_typing                            true
% 6.68/1.51  --prep_gs_sim                           true
% 6.68/1.51  --prep_unflatten                        true
% 6.68/1.51  --prep_res_sim                          true
% 6.68/1.51  --prep_upred                            true
% 6.68/1.51  --prep_sem_filter                       exhaustive
% 6.68/1.51  --prep_sem_filter_out                   false
% 6.68/1.51  --pred_elim                             true
% 6.68/1.51  --res_sim_input                         true
% 6.68/1.51  --eq_ax_congr_red                       true
% 6.68/1.51  --pure_diseq_elim                       true
% 6.68/1.51  --brand_transform                       false
% 6.68/1.51  --non_eq_to_eq                          false
% 6.68/1.51  --prep_def_merge                        true
% 6.68/1.51  --prep_def_merge_prop_impl              false
% 6.68/1.51  --prep_def_merge_mbd                    true
% 6.68/1.51  --prep_def_merge_tr_red                 false
% 6.68/1.51  --prep_def_merge_tr_cl                  false
% 6.68/1.51  --smt_preprocessing                     true
% 6.68/1.51  --smt_ac_axioms                         fast
% 6.68/1.51  --preprocessed_out                      false
% 6.68/1.51  --preprocessed_stats                    false
% 6.68/1.51  
% 6.68/1.51  ------ Abstraction refinement Options
% 6.68/1.51  
% 6.68/1.51  --abstr_ref                             []
% 6.68/1.51  --abstr_ref_prep                        false
% 6.68/1.51  --abstr_ref_until_sat                   false
% 6.68/1.51  --abstr_ref_sig_restrict                funpre
% 6.68/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 6.68/1.51  --abstr_ref_under                       []
% 6.68/1.51  
% 6.68/1.51  ------ SAT Options
% 6.68/1.51  
% 6.68/1.51  --sat_mode                              false
% 6.68/1.51  --sat_fm_restart_options                ""
% 6.68/1.51  --sat_gr_def                            false
% 6.68/1.51  --sat_epr_types                         true
% 6.68/1.51  --sat_non_cyclic_types                  false
% 6.68/1.51  --sat_finite_models                     false
% 6.68/1.51  --sat_fm_lemmas                         false
% 6.68/1.51  --sat_fm_prep                           false
% 6.68/1.51  --sat_fm_uc_incr                        true
% 6.68/1.51  --sat_out_model                         small
% 6.68/1.51  --sat_out_clauses                       false
% 6.68/1.51  
% 6.68/1.51  ------ QBF Options
% 6.68/1.51  
% 6.68/1.51  --qbf_mode                              false
% 6.68/1.51  --qbf_elim_univ                         false
% 6.68/1.51  --qbf_dom_inst                          none
% 6.68/1.51  --qbf_dom_pre_inst                      false
% 6.68/1.51  --qbf_sk_in                             false
% 6.68/1.51  --qbf_pred_elim                         true
% 6.68/1.51  --qbf_split                             512
% 6.68/1.51  
% 6.68/1.51  ------ BMC1 Options
% 6.68/1.51  
% 6.68/1.51  --bmc1_incremental                      false
% 6.68/1.51  --bmc1_axioms                           reachable_all
% 6.68/1.51  --bmc1_min_bound                        0
% 6.68/1.51  --bmc1_max_bound                        -1
% 6.68/1.51  --bmc1_max_bound_default                -1
% 6.68/1.51  --bmc1_symbol_reachability              true
% 6.68/1.51  --bmc1_property_lemmas                  false
% 6.68/1.51  --bmc1_k_induction                      false
% 6.68/1.51  --bmc1_non_equiv_states                 false
% 6.68/1.51  --bmc1_deadlock                         false
% 6.68/1.51  --bmc1_ucm                              false
% 6.68/1.51  --bmc1_add_unsat_core                   none
% 6.68/1.51  --bmc1_unsat_core_children              false
% 6.68/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 6.68/1.51  --bmc1_out_stat                         full
% 6.68/1.51  --bmc1_ground_init                      false
% 6.68/1.51  --bmc1_pre_inst_next_state              false
% 6.68/1.51  --bmc1_pre_inst_state                   false
% 6.68/1.51  --bmc1_pre_inst_reach_state             false
% 6.68/1.51  --bmc1_out_unsat_core                   false
% 6.68/1.51  --bmc1_aig_witness_out                  false
% 6.68/1.51  --bmc1_verbose                          false
% 6.68/1.51  --bmc1_dump_clauses_tptp                false
% 6.68/1.51  --bmc1_dump_unsat_core_tptp             false
% 6.68/1.51  --bmc1_dump_file                        -
% 6.68/1.51  --bmc1_ucm_expand_uc_limit              128
% 6.68/1.51  --bmc1_ucm_n_expand_iterations          6
% 6.68/1.51  --bmc1_ucm_extend_mode                  1
% 6.68/1.51  --bmc1_ucm_init_mode                    2
% 6.68/1.51  --bmc1_ucm_cone_mode                    none
% 6.68/1.51  --bmc1_ucm_reduced_relation_type        0
% 6.68/1.51  --bmc1_ucm_relax_model                  4
% 6.68/1.51  --bmc1_ucm_full_tr_after_sat            true
% 6.68/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 6.68/1.51  --bmc1_ucm_layered_model                none
% 6.68/1.51  --bmc1_ucm_max_lemma_size               10
% 6.68/1.51  
% 6.68/1.51  ------ AIG Options
% 6.68/1.51  
% 6.68/1.51  --aig_mode                              false
% 6.68/1.51  
% 6.68/1.51  ------ Instantiation Options
% 6.68/1.51  
% 6.68/1.51  --instantiation_flag                    true
% 6.68/1.51  --inst_sos_flag                         false
% 6.68/1.51  --inst_sos_phase                        true
% 6.68/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.68/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.68/1.51  --inst_lit_sel_side                     num_symb
% 6.68/1.51  --inst_solver_per_active                1400
% 6.68/1.51  --inst_solver_calls_frac                1.
% 6.68/1.51  --inst_passive_queue_type               priority_queues
% 6.68/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.68/1.51  --inst_passive_queues_freq              [25;2]
% 6.68/1.51  --inst_dismatching                      true
% 6.68/1.51  --inst_eager_unprocessed_to_passive     true
% 6.68/1.51  --inst_prop_sim_given                   true
% 6.68/1.51  --inst_prop_sim_new                     false
% 6.68/1.51  --inst_subs_new                         false
% 6.68/1.51  --inst_eq_res_simp                      false
% 6.68/1.51  --inst_subs_given                       false
% 6.68/1.51  --inst_orphan_elimination               true
% 6.68/1.51  --inst_learning_loop_flag               true
% 6.68/1.51  --inst_learning_start                   3000
% 6.68/1.51  --inst_learning_factor                  2
% 6.68/1.51  --inst_start_prop_sim_after_learn       3
% 6.68/1.51  --inst_sel_renew                        solver
% 6.68/1.51  --inst_lit_activity_flag                true
% 6.68/1.51  --inst_restr_to_given                   false
% 6.68/1.51  --inst_activity_threshold               500
% 6.68/1.51  --inst_out_proof                        true
% 6.68/1.51  
% 6.68/1.51  ------ Resolution Options
% 6.68/1.51  
% 6.68/1.51  --resolution_flag                       true
% 6.68/1.51  --res_lit_sel                           adaptive
% 6.68/1.51  --res_lit_sel_side                      none
% 6.68/1.51  --res_ordering                          kbo
% 6.68/1.51  --res_to_prop_solver                    active
% 6.68/1.51  --res_prop_simpl_new                    false
% 6.68/1.51  --res_prop_simpl_given                  true
% 6.68/1.51  --res_passive_queue_type                priority_queues
% 6.68/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.68/1.51  --res_passive_queues_freq               [15;5]
% 6.68/1.51  --res_forward_subs                      full
% 6.68/1.51  --res_backward_subs                     full
% 6.68/1.51  --res_forward_subs_resolution           true
% 6.68/1.51  --res_backward_subs_resolution          true
% 6.68/1.51  --res_orphan_elimination                true
% 6.68/1.51  --res_time_limit                        2.
% 6.68/1.51  --res_out_proof                         true
% 6.68/1.51  
% 6.68/1.51  ------ Superposition Options
% 6.68/1.51  
% 6.68/1.51  --superposition_flag                    true
% 6.68/1.51  --sup_passive_queue_type                priority_queues
% 6.68/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.68/1.51  --sup_passive_queues_freq               [8;1;4]
% 6.68/1.51  --demod_completeness_check              fast
% 6.68/1.51  --demod_use_ground                      true
% 6.68/1.51  --sup_to_prop_solver                    passive
% 6.68/1.51  --sup_prop_simpl_new                    true
% 6.68/1.51  --sup_prop_simpl_given                  true
% 6.68/1.51  --sup_fun_splitting                     false
% 6.68/1.51  --sup_smt_interval                      50000
% 6.68/1.51  
% 6.68/1.51  ------ Superposition Simplification Setup
% 6.68/1.51  
% 6.68/1.51  --sup_indices_passive                   []
% 6.68/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.68/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.68/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.68/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 6.68/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.68/1.51  --sup_full_bw                           [BwDemod]
% 6.68/1.51  --sup_immed_triv                        [TrivRules]
% 6.68/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.68/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.68/1.51  --sup_immed_bw_main                     []
% 6.68/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.68/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 6.68/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.68/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.68/1.51  
% 6.68/1.51  ------ Combination Options
% 6.68/1.51  
% 6.68/1.51  --comb_res_mult                         3
% 6.68/1.51  --comb_sup_mult                         2
% 6.68/1.51  --comb_inst_mult                        10
% 6.68/1.51  
% 6.68/1.51  ------ Debug Options
% 6.68/1.51  
% 6.68/1.51  --dbg_backtrace                         false
% 6.68/1.51  --dbg_dump_prop_clauses                 false
% 6.68/1.51  --dbg_dump_prop_clauses_file            -
% 6.68/1.51  --dbg_out_stat                          false
% 6.68/1.51  ------ Parsing...
% 6.68/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.68/1.51  
% 6.68/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 6.68/1.51  
% 6.68/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.68/1.51  
% 6.68/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.68/1.51  ------ Proving...
% 6.68/1.51  ------ Problem Properties 
% 6.68/1.51  
% 6.68/1.51  
% 6.68/1.51  clauses                                 38
% 6.68/1.51  conjectures                             4
% 6.68/1.51  EPR                                     8
% 6.68/1.51  Horn                                    32
% 6.68/1.51  unary                                   7
% 6.68/1.51  binary                                  13
% 6.68/1.51  lits                                    103
% 6.68/1.51  lits eq                                 35
% 6.68/1.51  fd_pure                                 0
% 6.68/1.51  fd_pseudo                               0
% 6.68/1.51  fd_cond                                 3
% 6.68/1.51  fd_pseudo_cond                          1
% 6.68/1.51  AC symbols                              0
% 6.68/1.51  
% 6.68/1.51  ------ Schedule dynamic 5 is on 
% 6.68/1.51  
% 6.68/1.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.68/1.51  
% 6.68/1.51  
% 6.68/1.51  ------ 
% 6.68/1.51  Current options:
% 6.68/1.51  ------ 
% 6.68/1.51  
% 6.68/1.51  ------ Input Options
% 6.68/1.51  
% 6.68/1.51  --out_options                           all
% 6.68/1.51  --tptp_safe_out                         true
% 6.68/1.51  --problem_path                          ""
% 6.68/1.51  --include_path                          ""
% 6.68/1.51  --clausifier                            res/vclausify_rel
% 6.68/1.51  --clausifier_options                    --mode clausify
% 6.68/1.51  --stdin                                 false
% 6.68/1.51  --stats_out                             all
% 6.68/1.51  
% 6.68/1.51  ------ General Options
% 6.68/1.51  
% 6.68/1.51  --fof                                   false
% 6.68/1.51  --time_out_real                         305.
% 6.68/1.51  --time_out_virtual                      -1.
% 6.68/1.51  --symbol_type_check                     false
% 6.68/1.51  --clausify_out                          false
% 6.68/1.51  --sig_cnt_out                           false
% 6.68/1.51  --trig_cnt_out                          false
% 6.68/1.51  --trig_cnt_out_tolerance                1.
% 6.68/1.51  --trig_cnt_out_sk_spl                   false
% 6.68/1.51  --abstr_cl_out                          false
% 6.68/1.51  
% 6.68/1.51  ------ Global Options
% 6.68/1.51  
% 6.68/1.51  --schedule                              default
% 6.68/1.51  --add_important_lit                     false
% 6.68/1.51  --prop_solver_per_cl                    1000
% 6.68/1.51  --min_unsat_core                        false
% 6.68/1.51  --soft_assumptions                      false
% 6.68/1.51  --soft_lemma_size                       3
% 6.68/1.51  --prop_impl_unit_size                   0
% 6.68/1.51  --prop_impl_unit                        []
% 6.68/1.51  --share_sel_clauses                     true
% 6.68/1.51  --reset_solvers                         false
% 6.68/1.51  --bc_imp_inh                            [conj_cone]
% 6.68/1.51  --conj_cone_tolerance                   3.
% 6.68/1.51  --extra_neg_conj                        none
% 6.68/1.51  --large_theory_mode                     true
% 6.68/1.51  --prolific_symb_bound                   200
% 6.68/1.51  --lt_threshold                          2000
% 6.68/1.51  --clause_weak_htbl                      true
% 6.68/1.51  --gc_record_bc_elim                     false
% 6.68/1.51  
% 6.68/1.51  ------ Preprocessing Options
% 6.68/1.51  
% 6.68/1.51  --preprocessing_flag                    true
% 6.68/1.51  --time_out_prep_mult                    0.1
% 6.68/1.51  --splitting_mode                        input
% 6.68/1.51  --splitting_grd                         true
% 6.68/1.51  --splitting_cvd                         false
% 6.68/1.51  --splitting_cvd_svl                     false
% 6.68/1.51  --splitting_nvd                         32
% 6.68/1.51  --sub_typing                            true
% 6.68/1.51  --prep_gs_sim                           true
% 6.68/1.51  --prep_unflatten                        true
% 6.68/1.51  --prep_res_sim                          true
% 6.68/1.51  --prep_upred                            true
% 6.68/1.51  --prep_sem_filter                       exhaustive
% 6.68/1.51  --prep_sem_filter_out                   false
% 6.68/1.51  --pred_elim                             true
% 6.68/1.51  --res_sim_input                         true
% 6.68/1.51  --eq_ax_congr_red                       true
% 6.68/1.51  --pure_diseq_elim                       true
% 6.68/1.51  --brand_transform                       false
% 6.68/1.51  --non_eq_to_eq                          false
% 6.68/1.51  --prep_def_merge                        true
% 6.68/1.51  --prep_def_merge_prop_impl              false
% 6.68/1.51  --prep_def_merge_mbd                    true
% 6.68/1.51  --prep_def_merge_tr_red                 false
% 6.68/1.51  --prep_def_merge_tr_cl                  false
% 6.68/1.51  --smt_preprocessing                     true
% 6.68/1.51  --smt_ac_axioms                         fast
% 6.68/1.51  --preprocessed_out                      false
% 6.68/1.51  --preprocessed_stats                    false
% 6.68/1.51  
% 6.68/1.51  ------ Abstraction refinement Options
% 6.68/1.51  
% 6.68/1.51  --abstr_ref                             []
% 6.68/1.51  --abstr_ref_prep                        false
% 6.68/1.51  --abstr_ref_until_sat                   false
% 6.68/1.51  --abstr_ref_sig_restrict                funpre
% 6.68/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 6.68/1.51  --abstr_ref_under                       []
% 6.68/1.51  
% 6.68/1.51  ------ SAT Options
% 6.68/1.51  
% 6.68/1.51  --sat_mode                              false
% 6.68/1.51  --sat_fm_restart_options                ""
% 6.68/1.51  --sat_gr_def                            false
% 6.68/1.51  --sat_epr_types                         true
% 6.68/1.51  --sat_non_cyclic_types                  false
% 6.68/1.51  --sat_finite_models                     false
% 6.68/1.51  --sat_fm_lemmas                         false
% 6.68/1.51  --sat_fm_prep                           false
% 6.68/1.51  --sat_fm_uc_incr                        true
% 6.68/1.51  --sat_out_model                         small
% 6.68/1.51  --sat_out_clauses                       false
% 6.68/1.51  
% 6.68/1.51  ------ QBF Options
% 6.68/1.51  
% 6.68/1.51  --qbf_mode                              false
% 6.68/1.51  --qbf_elim_univ                         false
% 6.68/1.51  --qbf_dom_inst                          none
% 6.68/1.51  --qbf_dom_pre_inst                      false
% 6.68/1.51  --qbf_sk_in                             false
% 6.68/1.51  --qbf_pred_elim                         true
% 6.68/1.51  --qbf_split                             512
% 6.68/1.51  
% 6.68/1.51  ------ BMC1 Options
% 6.68/1.51  
% 6.68/1.51  --bmc1_incremental                      false
% 6.68/1.51  --bmc1_axioms                           reachable_all
% 6.68/1.51  --bmc1_min_bound                        0
% 6.68/1.51  --bmc1_max_bound                        -1
% 6.68/1.51  --bmc1_max_bound_default                -1
% 6.68/1.51  --bmc1_symbol_reachability              true
% 6.68/1.51  --bmc1_property_lemmas                  false
% 6.68/1.51  --bmc1_k_induction                      false
% 6.68/1.51  --bmc1_non_equiv_states                 false
% 6.68/1.51  --bmc1_deadlock                         false
% 6.68/1.51  --bmc1_ucm                              false
% 6.68/1.51  --bmc1_add_unsat_core                   none
% 6.68/1.51  --bmc1_unsat_core_children              false
% 6.68/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 6.68/1.51  --bmc1_out_stat                         full
% 6.68/1.51  --bmc1_ground_init                      false
% 6.68/1.51  --bmc1_pre_inst_next_state              false
% 6.68/1.51  --bmc1_pre_inst_state                   false
% 6.68/1.51  --bmc1_pre_inst_reach_state             false
% 6.68/1.51  --bmc1_out_unsat_core                   false
% 6.68/1.51  --bmc1_aig_witness_out                  false
% 6.68/1.51  --bmc1_verbose                          false
% 6.68/1.51  --bmc1_dump_clauses_tptp                false
% 6.68/1.51  --bmc1_dump_unsat_core_tptp             false
% 6.68/1.51  --bmc1_dump_file                        -
% 6.68/1.51  --bmc1_ucm_expand_uc_limit              128
% 6.68/1.51  --bmc1_ucm_n_expand_iterations          6
% 6.68/1.51  --bmc1_ucm_extend_mode                  1
% 6.68/1.51  --bmc1_ucm_init_mode                    2
% 6.68/1.51  --bmc1_ucm_cone_mode                    none
% 6.68/1.51  --bmc1_ucm_reduced_relation_type        0
% 6.68/1.51  --bmc1_ucm_relax_model                  4
% 6.68/1.51  --bmc1_ucm_full_tr_after_sat            true
% 6.68/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 6.68/1.51  --bmc1_ucm_layered_model                none
% 6.68/1.51  --bmc1_ucm_max_lemma_size               10
% 6.68/1.51  
% 6.68/1.51  ------ AIG Options
% 6.68/1.51  
% 6.68/1.51  --aig_mode                              false
% 6.68/1.51  
% 6.68/1.51  ------ Instantiation Options
% 6.68/1.51  
% 6.68/1.51  --instantiation_flag                    true
% 6.68/1.51  --inst_sos_flag                         false
% 6.68/1.51  --inst_sos_phase                        true
% 6.68/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.68/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.68/1.51  --inst_lit_sel_side                     none
% 6.68/1.51  --inst_solver_per_active                1400
% 6.68/1.51  --inst_solver_calls_frac                1.
% 6.68/1.51  --inst_passive_queue_type               priority_queues
% 6.68/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.68/1.51  --inst_passive_queues_freq              [25;2]
% 6.68/1.51  --inst_dismatching                      true
% 6.68/1.51  --inst_eager_unprocessed_to_passive     true
% 6.68/1.51  --inst_prop_sim_given                   true
% 6.68/1.51  --inst_prop_sim_new                     false
% 6.68/1.51  --inst_subs_new                         false
% 6.68/1.51  --inst_eq_res_simp                      false
% 6.68/1.51  --inst_subs_given                       false
% 6.68/1.51  --inst_orphan_elimination               true
% 6.68/1.51  --inst_learning_loop_flag               true
% 6.68/1.51  --inst_learning_start                   3000
% 6.68/1.51  --inst_learning_factor                  2
% 6.68/1.51  --inst_start_prop_sim_after_learn       3
% 6.68/1.51  --inst_sel_renew                        solver
% 6.68/1.51  --inst_lit_activity_flag                true
% 6.68/1.51  --inst_restr_to_given                   false
% 6.68/1.51  --inst_activity_threshold               500
% 6.68/1.51  --inst_out_proof                        true
% 6.68/1.51  
% 6.68/1.51  ------ Resolution Options
% 6.68/1.51  
% 6.68/1.51  --resolution_flag                       false
% 6.68/1.51  --res_lit_sel                           adaptive
% 6.68/1.51  --res_lit_sel_side                      none
% 6.68/1.51  --res_ordering                          kbo
% 6.68/1.51  --res_to_prop_solver                    active
% 6.68/1.51  --res_prop_simpl_new                    false
% 6.68/1.51  --res_prop_simpl_given                  true
% 6.68/1.51  --res_passive_queue_type                priority_queues
% 6.68/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.68/1.51  --res_passive_queues_freq               [15;5]
% 6.68/1.51  --res_forward_subs                      full
% 6.68/1.51  --res_backward_subs                     full
% 6.68/1.51  --res_forward_subs_resolution           true
% 6.68/1.51  --res_backward_subs_resolution          true
% 6.68/1.51  --res_orphan_elimination                true
% 6.68/1.51  --res_time_limit                        2.
% 6.68/1.51  --res_out_proof                         true
% 6.68/1.51  
% 6.68/1.51  ------ Superposition Options
% 6.68/1.51  
% 6.68/1.51  --superposition_flag                    true
% 6.68/1.51  --sup_passive_queue_type                priority_queues
% 6.68/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.68/1.51  --sup_passive_queues_freq               [8;1;4]
% 6.68/1.51  --demod_completeness_check              fast
% 6.68/1.51  --demod_use_ground                      true
% 6.68/1.51  --sup_to_prop_solver                    passive
% 6.68/1.51  --sup_prop_simpl_new                    true
% 6.68/1.51  --sup_prop_simpl_given                  true
% 6.68/1.51  --sup_fun_splitting                     false
% 6.68/1.51  --sup_smt_interval                      50000
% 6.68/1.51  
% 6.68/1.51  ------ Superposition Simplification Setup
% 6.68/1.51  
% 6.68/1.51  --sup_indices_passive                   []
% 6.68/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.68/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.68/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.68/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 6.68/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.68/1.51  --sup_full_bw                           [BwDemod]
% 6.68/1.51  --sup_immed_triv                        [TrivRules]
% 6.68/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.68/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.68/1.51  --sup_immed_bw_main                     []
% 6.68/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.68/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 6.68/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.68/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.68/1.51  
% 6.68/1.51  ------ Combination Options
% 6.68/1.51  
% 6.68/1.51  --comb_res_mult                         3
% 6.68/1.51  --comb_sup_mult                         2
% 6.68/1.51  --comb_inst_mult                        10
% 6.68/1.51  
% 6.68/1.51  ------ Debug Options
% 6.68/1.51  
% 6.68/1.51  --dbg_backtrace                         false
% 6.68/1.51  --dbg_dump_prop_clauses                 false
% 6.68/1.51  --dbg_dump_prop_clauses_file            -
% 6.68/1.51  --dbg_out_stat                          false
% 6.68/1.51  
% 6.68/1.51  
% 6.68/1.51  
% 6.68/1.51  
% 6.68/1.51  ------ Proving...
% 6.68/1.51  
% 6.68/1.51  
% 6.68/1.51  % SZS status Theorem for theBenchmark.p
% 6.68/1.51  
% 6.68/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 6.68/1.51  
% 6.68/1.51  fof(f19,conjecture,(
% 6.68/1.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 6.68/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.68/1.51  
% 6.68/1.51  fof(f20,negated_conjecture,(
% 6.68/1.51    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 6.68/1.51    inference(negated_conjecture,[],[f19])).
% 6.68/1.51  
% 6.68/1.51  fof(f39,plain,(
% 6.68/1.51    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 6.68/1.51    inference(ennf_transformation,[],[f20])).
% 6.68/1.51  
% 6.68/1.51  fof(f40,plain,(
% 6.68/1.51    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 6.68/1.51    inference(flattening,[],[f39])).
% 6.68/1.51  
% 6.68/1.51  fof(f51,plain,(
% 6.68/1.51    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK3,sK2) | ~v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & r1_tarski(sK3,sK1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4))),
% 6.68/1.51    introduced(choice_axiom,[])).
% 6.68/1.51  
% 6.68/1.51  fof(f52,plain,(
% 6.68/1.51    (~m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK3,sK2) | ~v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & r1_tarski(sK3,sK1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)),
% 6.68/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f40,f51])).
% 6.68/1.51  
% 6.68/1.51  fof(f88,plain,(
% 6.68/1.51    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 6.68/1.51    inference(cnf_transformation,[],[f52])).
% 6.68/1.51  
% 6.68/1.51  fof(f17,axiom,(
% 6.68/1.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 6.68/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.68/1.51  
% 6.68/1.51  fof(f35,plain,(
% 6.68/1.51    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 6.68/1.51    inference(ennf_transformation,[],[f17])).
% 6.68/1.51  
% 6.68/1.51  fof(f36,plain,(
% 6.68/1.51    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 6.68/1.51    inference(flattening,[],[f35])).
% 6.68/1.51  
% 6.68/1.51  fof(f82,plain,(
% 6.68/1.51    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 6.68/1.51    inference(cnf_transformation,[],[f36])).
% 6.68/1.51  
% 6.68/1.51  fof(f86,plain,(
% 6.68/1.51    v1_funct_1(sK4)),
% 6.68/1.51    inference(cnf_transformation,[],[f52])).
% 6.68/1.51  
% 6.68/1.51  fof(f16,axiom,(
% 6.68/1.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 6.68/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.68/1.51  
% 6.68/1.51  fof(f33,plain,(
% 6.68/1.51    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 6.68/1.51    inference(ennf_transformation,[],[f16])).
% 6.68/1.51  
% 6.68/1.51  fof(f34,plain,(
% 6.68/1.51    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 6.68/1.51    inference(flattening,[],[f33])).
% 6.68/1.51  
% 6.68/1.51  fof(f81,plain,(
% 6.68/1.51    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 6.68/1.51    inference(cnf_transformation,[],[f34])).
% 6.68/1.51  
% 6.68/1.51  fof(f14,axiom,(
% 6.68/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 6.68/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.68/1.51  
% 6.68/1.51  fof(f30,plain,(
% 6.68/1.51    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.68/1.51    inference(ennf_transformation,[],[f14])).
% 6.68/1.51  
% 6.68/1.51  fof(f73,plain,(
% 6.68/1.51    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.68/1.51    inference(cnf_transformation,[],[f30])).
% 6.68/1.51  
% 6.68/1.51  fof(f12,axiom,(
% 6.68/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 6.68/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.68/1.51  
% 6.68/1.51  fof(f28,plain,(
% 6.68/1.51    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.68/1.51    inference(ennf_transformation,[],[f12])).
% 6.68/1.51  
% 6.68/1.51  fof(f71,plain,(
% 6.68/1.51    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.68/1.51    inference(cnf_transformation,[],[f28])).
% 6.68/1.51  
% 6.68/1.51  fof(f6,axiom,(
% 6.68/1.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 6.68/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.68/1.51  
% 6.68/1.51  fof(f49,plain,(
% 6.68/1.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 6.68/1.51    inference(nnf_transformation,[],[f6])).
% 6.68/1.51  
% 6.68/1.51  fof(f64,plain,(
% 6.68/1.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 6.68/1.51    inference(cnf_transformation,[],[f49])).
% 6.68/1.51  
% 6.68/1.51  fof(f89,plain,(
% 6.68/1.51    r1_tarski(sK3,sK1)),
% 6.68/1.51    inference(cnf_transformation,[],[f52])).
% 6.68/1.51  
% 6.68/1.51  fof(f15,axiom,(
% 6.68/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 6.68/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.68/1.51  
% 6.68/1.51  fof(f31,plain,(
% 6.68/1.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.68/1.51    inference(ennf_transformation,[],[f15])).
% 6.68/1.51  
% 6.68/1.51  fof(f32,plain,(
% 6.68/1.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.68/1.51    inference(flattening,[],[f31])).
% 6.68/1.51  
% 6.68/1.51  fof(f50,plain,(
% 6.68/1.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.68/1.51    inference(nnf_transformation,[],[f32])).
% 6.68/1.51  
% 6.68/1.51  fof(f74,plain,(
% 6.68/1.51    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.68/1.51    inference(cnf_transformation,[],[f50])).
% 6.68/1.51  
% 6.68/1.51  fof(f87,plain,(
% 6.68/1.51    v1_funct_2(sK4,sK1,sK2)),
% 6.68/1.51    inference(cnf_transformation,[],[f52])).
% 6.68/1.51  
% 6.68/1.51  fof(f13,axiom,(
% 6.68/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 6.68/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.68/1.51  
% 6.68/1.51  fof(f29,plain,(
% 6.68/1.51    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.68/1.51    inference(ennf_transformation,[],[f13])).
% 6.68/1.51  
% 6.68/1.51  fof(f72,plain,(
% 6.68/1.51    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.68/1.51    inference(cnf_transformation,[],[f29])).
% 6.68/1.51  
% 6.68/1.51  fof(f10,axiom,(
% 6.68/1.51    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 6.68/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.68/1.51  
% 6.68/1.51  fof(f25,plain,(
% 6.68/1.51    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 6.68/1.51    inference(ennf_transformation,[],[f10])).
% 6.68/1.51  
% 6.68/1.51  fof(f26,plain,(
% 6.68/1.51    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 6.68/1.51    inference(flattening,[],[f25])).
% 6.68/1.51  
% 6.68/1.51  fof(f69,plain,(
% 6.68/1.51    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 6.68/1.51    inference(cnf_transformation,[],[f26])).
% 6.68/1.51  
% 6.68/1.51  fof(f11,axiom,(
% 6.68/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 6.68/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.68/1.51  
% 6.68/1.51  fof(f27,plain,(
% 6.68/1.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.68/1.51    inference(ennf_transformation,[],[f11])).
% 6.68/1.51  
% 6.68/1.51  fof(f70,plain,(
% 6.68/1.51    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.68/1.51    inference(cnf_transformation,[],[f27])).
% 6.68/1.51  
% 6.68/1.51  fof(f18,axiom,(
% 6.68/1.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 6.68/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.68/1.51  
% 6.68/1.51  fof(f37,plain,(
% 6.68/1.51    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 6.68/1.51    inference(ennf_transformation,[],[f18])).
% 6.68/1.51  
% 6.68/1.51  fof(f38,plain,(
% 6.68/1.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 6.68/1.51    inference(flattening,[],[f37])).
% 6.68/1.51  
% 6.68/1.51  fof(f85,plain,(
% 6.68/1.51    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 6.68/1.51    inference(cnf_transformation,[],[f38])).
% 6.68/1.51  
% 6.68/1.51  fof(f80,plain,(
% 6.68/1.51    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 6.68/1.51    inference(cnf_transformation,[],[f34])).
% 6.68/1.51  
% 6.68/1.51  fof(f84,plain,(
% 6.68/1.51    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 6.68/1.51    inference(cnf_transformation,[],[f38])).
% 6.68/1.51  
% 6.68/1.51  fof(f91,plain,(
% 6.68/1.51    ~m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK3,sK2) | ~v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))),
% 6.68/1.51    inference(cnf_transformation,[],[f52])).
% 6.68/1.51  
% 6.68/1.51  fof(f90,plain,(
% 6.68/1.51    k1_xboole_0 = sK1 | k1_xboole_0 != sK2),
% 6.68/1.51    inference(cnf_transformation,[],[f52])).
% 6.68/1.51  
% 6.68/1.51  fof(f5,axiom,(
% 6.68/1.51    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 6.68/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.68/1.51  
% 6.68/1.51  fof(f47,plain,(
% 6.68/1.51    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 6.68/1.51    inference(nnf_transformation,[],[f5])).
% 6.68/1.51  
% 6.68/1.51  fof(f48,plain,(
% 6.68/1.51    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 6.68/1.51    inference(flattening,[],[f47])).
% 6.68/1.51  
% 6.68/1.51  fof(f62,plain,(
% 6.68/1.51    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 6.68/1.51    inference(cnf_transformation,[],[f48])).
% 6.68/1.51  
% 6.68/1.51  fof(f95,plain,(
% 6.68/1.51    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 6.68/1.51    inference(equality_resolution,[],[f62])).
% 6.68/1.51  
% 6.68/1.51  fof(f2,axiom,(
% 6.68/1.51    v1_xboole_0(k1_xboole_0)),
% 6.68/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.68/1.51  
% 6.68/1.51  fof(f56,plain,(
% 6.68/1.51    v1_xboole_0(k1_xboole_0)),
% 6.68/1.51    inference(cnf_transformation,[],[f2])).
% 6.68/1.51  
% 6.68/1.51  fof(f7,axiom,(
% 6.68/1.51    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 6.68/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.68/1.51  
% 6.68/1.51  fof(f22,plain,(
% 6.68/1.51    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 6.68/1.51    inference(ennf_transformation,[],[f7])).
% 6.68/1.51  
% 6.68/1.51  fof(f66,plain,(
% 6.68/1.51    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 6.68/1.51    inference(cnf_transformation,[],[f22])).
% 6.68/1.51  
% 6.68/1.51  fof(f65,plain,(
% 6.68/1.51    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 6.68/1.51    inference(cnf_transformation,[],[f49])).
% 6.68/1.51  
% 6.68/1.51  fof(f4,axiom,(
% 6.68/1.51    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 6.68/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.68/1.51  
% 6.68/1.51  fof(f60,plain,(
% 6.68/1.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 6.68/1.51    inference(cnf_transformation,[],[f4])).
% 6.68/1.51  
% 6.68/1.51  fof(f3,axiom,(
% 6.68/1.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 6.68/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.68/1.51  
% 6.68/1.51  fof(f45,plain,(
% 6.68/1.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.68/1.51    inference(nnf_transformation,[],[f3])).
% 6.68/1.51  
% 6.68/1.51  fof(f46,plain,(
% 6.68/1.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.68/1.51    inference(flattening,[],[f45])).
% 6.68/1.51  
% 6.68/1.51  fof(f59,plain,(
% 6.68/1.51    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 6.68/1.51    inference(cnf_transformation,[],[f46])).
% 6.68/1.51  
% 6.68/1.51  fof(f1,axiom,(
% 6.68/1.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 6.68/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.68/1.51  
% 6.68/1.51  fof(f21,plain,(
% 6.68/1.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 6.68/1.51    inference(ennf_transformation,[],[f1])).
% 6.68/1.51  
% 6.68/1.51  fof(f41,plain,(
% 6.68/1.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 6.68/1.51    inference(nnf_transformation,[],[f21])).
% 6.68/1.51  
% 6.68/1.51  fof(f42,plain,(
% 6.68/1.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 6.68/1.51    inference(rectify,[],[f41])).
% 6.68/1.51  
% 6.68/1.51  fof(f43,plain,(
% 6.68/1.51    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 6.68/1.51    introduced(choice_axiom,[])).
% 6.68/1.51  
% 6.68/1.51  fof(f44,plain,(
% 6.68/1.51    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 6.68/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).
% 6.68/1.51  
% 6.68/1.51  fof(f54,plain,(
% 6.68/1.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 6.68/1.51    inference(cnf_transformation,[],[f44])).
% 6.68/1.51  
% 6.68/1.51  fof(f57,plain,(
% 6.68/1.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 6.68/1.51    inference(cnf_transformation,[],[f46])).
% 6.68/1.51  
% 6.68/1.51  fof(f93,plain,(
% 6.68/1.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 6.68/1.51    inference(equality_resolution,[],[f57])).
% 6.68/1.51  
% 6.68/1.51  fof(f9,axiom,(
% 6.68/1.51    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 6.68/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.68/1.51  
% 6.68/1.51  fof(f24,plain,(
% 6.68/1.51    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 6.68/1.51    inference(ennf_transformation,[],[f9])).
% 6.68/1.51  
% 6.68/1.51  fof(f68,plain,(
% 6.68/1.51    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 6.68/1.51    inference(cnf_transformation,[],[f24])).
% 6.68/1.51  
% 6.68/1.51  fof(f61,plain,(
% 6.68/1.51    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 6.68/1.51    inference(cnf_transformation,[],[f48])).
% 6.68/1.51  
% 6.68/1.51  cnf(c_36,negated_conjecture,
% 6.68/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 6.68/1.51      inference(cnf_transformation,[],[f88]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_1835,plain,
% 6.68/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 6.68/1.51      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_29,plain,
% 6.68/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.68/1.51      | ~ v1_funct_1(X0)
% 6.68/1.51      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 6.68/1.51      inference(cnf_transformation,[],[f82]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_1838,plain,
% 6.68/1.51      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 6.68/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 6.68/1.51      | v1_funct_1(X2) != iProver_top ),
% 6.68/1.51      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_4437,plain,
% 6.68/1.51      ( k2_partfun1(sK1,sK2,sK4,X0) = k7_relat_1(sK4,X0)
% 6.68/1.51      | v1_funct_1(sK4) != iProver_top ),
% 6.68/1.51      inference(superposition,[status(thm)],[c_1835,c_1838]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_38,negated_conjecture,
% 6.68/1.51      ( v1_funct_1(sK4) ),
% 6.68/1.51      inference(cnf_transformation,[],[f86]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_2232,plain,
% 6.68/1.51      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 6.68/1.51      | ~ v1_funct_1(sK4)
% 6.68/1.51      | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2) ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_29]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_2361,plain,
% 6.68/1.51      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 6.68/1.51      | ~ v1_funct_1(sK4)
% 6.68/1.51      | k2_partfun1(sK1,sK2,sK4,X0) = k7_relat_1(sK4,X0) ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_2232]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_4820,plain,
% 6.68/1.51      ( k2_partfun1(sK1,sK2,sK4,X0) = k7_relat_1(sK4,X0) ),
% 6.68/1.51      inference(global_propositional_subsumption,
% 6.68/1.51                [status(thm)],
% 6.68/1.51                [c_4437,c_38,c_36,c_2361]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_27,plain,
% 6.68/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.68/1.51      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.68/1.51      | ~ v1_funct_1(X0) ),
% 6.68/1.51      inference(cnf_transformation,[],[f81]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_1840,plain,
% 6.68/1.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 6.68/1.51      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 6.68/1.51      | v1_funct_1(X0) != iProver_top ),
% 6.68/1.51      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_6474,plain,
% 6.68/1.51      ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top
% 6.68/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 6.68/1.51      | v1_funct_1(sK4) != iProver_top ),
% 6.68/1.51      inference(superposition,[status(thm)],[c_4820,c_1840]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_39,plain,
% 6.68/1.51      ( v1_funct_1(sK4) = iProver_top ),
% 6.68/1.51      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_41,plain,
% 6.68/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 6.68/1.51      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_6906,plain,
% 6.68/1.51      ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 6.68/1.51      inference(global_propositional_subsumption,
% 6.68/1.51                [status(thm)],
% 6.68/1.51                [c_6474,c_39,c_41]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_20,plain,
% 6.68/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.68/1.51      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 6.68/1.51      inference(cnf_transformation,[],[f73]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_1841,plain,
% 6.68/1.51      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 6.68/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 6.68/1.51      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_6918,plain,
% 6.68/1.51      ( k2_relset_1(sK1,sK2,k7_relat_1(sK4,X0)) = k2_relat_1(k7_relat_1(sK4,X0)) ),
% 6.68/1.51      inference(superposition,[status(thm)],[c_6906,c_1841]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_18,plain,
% 6.68/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.68/1.51      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 6.68/1.51      inference(cnf_transformation,[],[f71]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_1843,plain,
% 6.68/1.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 6.68/1.51      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 6.68/1.51      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_7200,plain,
% 6.68/1.51      ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 6.68/1.51      | m1_subset_1(k2_relat_1(k7_relat_1(sK4,X0)),k1_zfmisc_1(sK2)) = iProver_top ),
% 6.68/1.51      inference(superposition,[status(thm)],[c_6918,c_1843]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_9882,plain,
% 6.68/1.51      ( m1_subset_1(k2_relat_1(k7_relat_1(sK4,X0)),k1_zfmisc_1(sK2)) = iProver_top ),
% 6.68/1.51      inference(global_propositional_subsumption,
% 6.68/1.51                [status(thm)],
% 6.68/1.51                [c_7200,c_39,c_41,c_6474]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_12,plain,
% 6.68/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 6.68/1.51      inference(cnf_transformation,[],[f64]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_1848,plain,
% 6.68/1.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 6.68/1.51      | r1_tarski(X0,X1) = iProver_top ),
% 6.68/1.51      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_9889,plain,
% 6.68/1.51      ( r1_tarski(k2_relat_1(k7_relat_1(sK4,X0)),sK2) = iProver_top ),
% 6.68/1.51      inference(superposition,[status(thm)],[c_9882,c_1848]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_35,negated_conjecture,
% 6.68/1.51      ( r1_tarski(sK3,sK1) ),
% 6.68/1.51      inference(cnf_transformation,[],[f89]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_1836,plain,
% 6.68/1.51      ( r1_tarski(sK3,sK1) = iProver_top ),
% 6.68/1.51      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_26,plain,
% 6.68/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 6.68/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.68/1.51      | k1_relset_1(X1,X2,X0) = X1
% 6.68/1.51      | k1_xboole_0 = X2 ),
% 6.68/1.51      inference(cnf_transformation,[],[f74]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_37,negated_conjecture,
% 6.68/1.51      ( v1_funct_2(sK4,sK1,sK2) ),
% 6.68/1.51      inference(cnf_transformation,[],[f87]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_650,plain,
% 6.68/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.68/1.51      | k1_relset_1(X1,X2,X0) = X1
% 6.68/1.51      | sK4 != X0
% 6.68/1.51      | sK2 != X2
% 6.68/1.51      | sK1 != X1
% 6.68/1.51      | k1_xboole_0 = X2 ),
% 6.68/1.51      inference(resolution_lifted,[status(thm)],[c_26,c_37]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_651,plain,
% 6.68/1.51      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 6.68/1.51      | k1_relset_1(sK1,sK2,sK4) = sK1
% 6.68/1.51      | k1_xboole_0 = sK2 ),
% 6.68/1.51      inference(unflattening,[status(thm)],[c_650]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_653,plain,
% 6.68/1.51      ( k1_relset_1(sK1,sK2,sK4) = sK1 | k1_xboole_0 = sK2 ),
% 6.68/1.51      inference(global_propositional_subsumption,
% 6.68/1.51                [status(thm)],
% 6.68/1.51                [c_651,c_36]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_19,plain,
% 6.68/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.68/1.51      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 6.68/1.51      inference(cnf_transformation,[],[f72]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_1842,plain,
% 6.68/1.51      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 6.68/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 6.68/1.51      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_3767,plain,
% 6.68/1.51      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 6.68/1.51      inference(superposition,[status(thm)],[c_1835,c_1842]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_4086,plain,
% 6.68/1.51      ( k1_relat_1(sK4) = sK1 | sK2 = k1_xboole_0 ),
% 6.68/1.51      inference(superposition,[status(thm)],[c_653,c_3767]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_16,plain,
% 6.68/1.51      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 6.68/1.51      | ~ v1_relat_1(X1)
% 6.68/1.51      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 6.68/1.51      inference(cnf_transformation,[],[f69]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_1845,plain,
% 6.68/1.51      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 6.68/1.51      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 6.68/1.51      | v1_relat_1(X0) != iProver_top ),
% 6.68/1.51      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_5547,plain,
% 6.68/1.51      ( k1_relat_1(k7_relat_1(sK4,X0)) = X0
% 6.68/1.51      | sK2 = k1_xboole_0
% 6.68/1.51      | r1_tarski(X0,sK1) != iProver_top
% 6.68/1.51      | v1_relat_1(sK4) != iProver_top ),
% 6.68/1.51      inference(superposition,[status(thm)],[c_4086,c_1845]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_17,plain,
% 6.68/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.68/1.51      | v1_relat_1(X0) ),
% 6.68/1.51      inference(cnf_transformation,[],[f70]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_2153,plain,
% 6.68/1.51      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 6.68/1.51      | v1_relat_1(sK4) ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_17]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_2154,plain,
% 6.68/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 6.68/1.51      | v1_relat_1(sK4) = iProver_top ),
% 6.68/1.51      inference(predicate_to_equality,[status(thm)],[c_2153]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_5714,plain,
% 6.68/1.51      ( r1_tarski(X0,sK1) != iProver_top
% 6.68/1.51      | sK2 = k1_xboole_0
% 6.68/1.51      | k1_relat_1(k7_relat_1(sK4,X0)) = X0 ),
% 6.68/1.51      inference(global_propositional_subsumption,
% 6.68/1.51                [status(thm)],
% 6.68/1.51                [c_5547,c_41,c_2154]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_5715,plain,
% 6.68/1.51      ( k1_relat_1(k7_relat_1(sK4,X0)) = X0
% 6.68/1.51      | sK2 = k1_xboole_0
% 6.68/1.51      | r1_tarski(X0,sK1) != iProver_top ),
% 6.68/1.51      inference(renaming,[status(thm)],[c_5714]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_5726,plain,
% 6.68/1.51      ( k1_relat_1(k7_relat_1(sK4,sK3)) = sK3 | sK2 = k1_xboole_0 ),
% 6.68/1.51      inference(superposition,[status(thm)],[c_1836,c_5715]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_30,plain,
% 6.68/1.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 6.68/1.51      | ~ r1_tarski(k2_relat_1(X0),X1)
% 6.68/1.51      | ~ v1_funct_1(X0)
% 6.68/1.51      | ~ v1_relat_1(X0) ),
% 6.68/1.51      inference(cnf_transformation,[],[f85]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_1837,plain,
% 6.68/1.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 6.68/1.51      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 6.68/1.51      | v1_funct_1(X0) != iProver_top
% 6.68/1.51      | v1_relat_1(X0) != iProver_top ),
% 6.68/1.51      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_5809,plain,
% 6.68/1.51      ( sK2 = k1_xboole_0
% 6.68/1.51      | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
% 6.68/1.51      | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK3)),X0) != iProver_top
% 6.68/1.51      | v1_funct_1(k7_relat_1(sK4,sK3)) != iProver_top
% 6.68/1.51      | v1_relat_1(k7_relat_1(sK4,sK3)) != iProver_top ),
% 6.68/1.51      inference(superposition,[status(thm)],[c_5726,c_1837]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_28,plain,
% 6.68/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.68/1.51      | ~ v1_funct_1(X0)
% 6.68/1.51      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 6.68/1.51      inference(cnf_transformation,[],[f80]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_1839,plain,
% 6.68/1.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 6.68/1.51      | v1_funct_1(X0) != iProver_top
% 6.68/1.51      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
% 6.68/1.51      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_5194,plain,
% 6.68/1.51      ( v1_funct_1(k2_partfun1(sK1,sK2,sK4,X0)) = iProver_top
% 6.68/1.51      | v1_funct_1(sK4) != iProver_top ),
% 6.68/1.51      inference(superposition,[status(thm)],[c_1835,c_1839]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_5220,plain,
% 6.68/1.51      ( v1_funct_1(k7_relat_1(sK4,X0)) = iProver_top
% 6.68/1.51      | v1_funct_1(sK4) != iProver_top ),
% 6.68/1.51      inference(light_normalisation,[status(thm)],[c_5194,c_4820]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_5706,plain,
% 6.68/1.51      ( v1_funct_1(k7_relat_1(sK4,X0)) = iProver_top ),
% 6.68/1.51      inference(global_propositional_subsumption,
% 6.68/1.51                [status(thm)],
% 6.68/1.51                [c_5220,c_39]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_5984,plain,
% 6.68/1.51      ( sK2 = k1_xboole_0
% 6.68/1.51      | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
% 6.68/1.51      | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK3)),X0) != iProver_top
% 6.68/1.51      | v1_relat_1(k7_relat_1(sK4,sK3)) != iProver_top ),
% 6.68/1.51      inference(forward_subsumption_resolution,
% 6.68/1.51                [status(thm)],
% 6.68/1.51                [c_5809,c_5706]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_31,plain,
% 6.68/1.51      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 6.68/1.51      | ~ r1_tarski(k2_relat_1(X0),X1)
% 6.68/1.51      | ~ v1_funct_1(X0)
% 6.68/1.51      | ~ v1_relat_1(X0) ),
% 6.68/1.51      inference(cnf_transformation,[],[f84]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_33,negated_conjecture,
% 6.68/1.51      ( ~ v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK3,sK2)
% 6.68/1.51      | ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 6.68/1.51      | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3)) ),
% 6.68/1.51      inference(cnf_transformation,[],[f91]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_661,plain,
% 6.68/1.51      ( ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 6.68/1.51      | ~ r1_tarski(k2_relat_1(X0),X1)
% 6.68/1.51      | ~ v1_funct_1(X0)
% 6.68/1.51      | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))
% 6.68/1.51      | ~ v1_relat_1(X0)
% 6.68/1.51      | k2_partfun1(sK1,sK2,sK4,sK3) != X0
% 6.68/1.51      | k1_relat_1(X0) != sK3
% 6.68/1.51      | sK2 != X1 ),
% 6.68/1.51      inference(resolution_lifted,[status(thm)],[c_31,c_33]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_662,plain,
% 6.68/1.51      ( ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 6.68/1.51      | ~ r1_tarski(k2_relat_1(k2_partfun1(sK1,sK2,sK4,sK3)),sK2)
% 6.68/1.51      | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))
% 6.68/1.51      | ~ v1_relat_1(k2_partfun1(sK1,sK2,sK4,sK3))
% 6.68/1.51      | k1_relat_1(k2_partfun1(sK1,sK2,sK4,sK3)) != sK3 ),
% 6.68/1.51      inference(unflattening,[status(thm)],[c_661]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_674,plain,
% 6.68/1.51      ( ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 6.68/1.51      | ~ r1_tarski(k2_relat_1(k2_partfun1(sK1,sK2,sK4,sK3)),sK2)
% 6.68/1.51      | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))
% 6.68/1.51      | k1_relat_1(k2_partfun1(sK1,sK2,sK4,sK3)) != sK3 ),
% 6.68/1.51      inference(forward_subsumption_resolution,
% 6.68/1.51                [status(thm)],
% 6.68/1.51                [c_662,c_17]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_1824,plain,
% 6.68/1.51      ( k1_relat_1(k2_partfun1(sK1,sK2,sK4,sK3)) != sK3
% 6.68/1.51      | m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 6.68/1.51      | r1_tarski(k2_relat_1(k2_partfun1(sK1,sK2,sK4,sK3)),sK2) != iProver_top
% 6.68/1.51      | v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3)) != iProver_top ),
% 6.68/1.51      inference(predicate_to_equality,[status(thm)],[c_674]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_4826,plain,
% 6.68/1.51      ( k1_relat_1(k7_relat_1(sK4,sK3)) != sK3
% 6.68/1.51      | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 6.68/1.51      | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK3)),sK2) != iProver_top
% 6.68/1.51      | v1_funct_1(k7_relat_1(sK4,sK3)) != iProver_top ),
% 6.68/1.51      inference(demodulation,[status(thm)],[c_4820,c_1824]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_5810,plain,
% 6.68/1.51      ( sK2 = k1_xboole_0
% 6.68/1.51      | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 6.68/1.51      | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK3)),sK2) != iProver_top
% 6.68/1.51      | v1_funct_1(k7_relat_1(sK4,sK3)) != iProver_top ),
% 6.68/1.51      inference(superposition,[status(thm)],[c_5726,c_4826]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_5849,plain,
% 6.68/1.51      ( sK2 = k1_xboole_0
% 6.68/1.51      | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 6.68/1.51      | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK3)),sK2) != iProver_top ),
% 6.68/1.51      inference(forward_subsumption_resolution,
% 6.68/1.51                [status(thm)],
% 6.68/1.51                [c_5810,c_5706]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_5995,plain,
% 6.68/1.51      ( sK2 = k1_xboole_0
% 6.68/1.51      | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK3)),sK2) != iProver_top
% 6.68/1.51      | v1_relat_1(k7_relat_1(sK4,sK3)) != iProver_top ),
% 6.68/1.51      inference(superposition,[status(thm)],[c_5984,c_5849]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_1844,plain,
% 6.68/1.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 6.68/1.51      | v1_relat_1(X0) = iProver_top ),
% 6.68/1.51      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_6915,plain,
% 6.68/1.51      ( v1_relat_1(k7_relat_1(sK4,X0)) = iProver_top ),
% 6.68/1.51      inference(superposition,[status(thm)],[c_6906,c_1844]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_9472,plain,
% 6.68/1.51      ( sK2 = k1_xboole_0
% 6.68/1.51      | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK3)),sK2) != iProver_top ),
% 6.68/1.51      inference(forward_subsumption_resolution,
% 6.68/1.51                [status(thm)],
% 6.68/1.51                [c_5995,c_6915]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_20925,plain,
% 6.68/1.51      ( sK2 = k1_xboole_0 ),
% 6.68/1.51      inference(superposition,[status(thm)],[c_9889,c_9472]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_21164,plain,
% 6.68/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
% 6.68/1.51      inference(demodulation,[status(thm)],[c_20925,c_1835]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_34,negated_conjecture,
% 6.68/1.51      ( k1_xboole_0 != sK2 | k1_xboole_0 = sK1 ),
% 6.68/1.51      inference(cnf_transformation,[],[f90]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_21165,plain,
% 6.68/1.51      ( sK1 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 6.68/1.51      inference(demodulation,[status(thm)],[c_20925,c_34]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_21166,plain,
% 6.68/1.51      ( sK1 = k1_xboole_0 ),
% 6.68/1.51      inference(equality_resolution_simp,[status(thm)],[c_21165]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_21169,plain,
% 6.68/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 6.68/1.51      inference(light_normalisation,[status(thm)],[c_21164,c_21166]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_9,plain,
% 6.68/1.51      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 6.68/1.51      inference(cnf_transformation,[],[f95]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_21171,plain,
% 6.68/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 6.68/1.51      inference(demodulation,[status(thm)],[c_21169,c_9]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_1066,plain,
% 6.68/1.51      ( X0 != X1
% 6.68/1.51      | X2 != X3
% 6.68/1.51      | X4 != X5
% 6.68/1.51      | X6 != X7
% 6.68/1.51      | k2_partfun1(X0,X2,X4,X6) = k2_partfun1(X1,X3,X5,X7) ),
% 6.68/1.51      theory(equality) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_3045,plain,
% 6.68/1.51      ( X0 != X1
% 6.68/1.51      | X2 != sK4
% 6.68/1.51      | X3 != sK2
% 6.68/1.51      | X4 != sK1
% 6.68/1.51      | k2_partfun1(X4,X3,X2,X0) = k2_partfun1(sK1,sK2,sK4,X1) ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_1066]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_7787,plain,
% 6.68/1.51      ( X0 != X1
% 6.68/1.51      | X2 != sK4
% 6.68/1.51      | X3 != sK1
% 6.68/1.51      | k2_partfun1(X3,sK2,X2,X0) = k2_partfun1(sK1,sK2,sK4,X1)
% 6.68/1.51      | sK2 != sK2 ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_3045]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_16896,plain,
% 6.68/1.51      ( k2_partfun1(sK1,sK2,sK4,sK3) = k2_partfun1(sK1,sK2,sK4,X0)
% 6.68/1.51      | sK3 != X0
% 6.68/1.51      | sK4 != sK4
% 6.68/1.51      | sK2 != sK2
% 6.68/1.51      | sK1 != sK1 ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_7787]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_16901,plain,
% 6.68/1.51      ( k2_partfun1(sK1,sK2,sK4,sK3) = k2_partfun1(sK1,sK2,sK4,k1_xboole_0)
% 6.68/1.51      | sK3 != k1_xboole_0
% 6.68/1.51      | sK4 != sK4
% 6.68/1.51      | sK2 != sK2
% 6.68/1.51      | sK1 != sK1 ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_16896]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_1057,plain,
% 6.68/1.51      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 6.68/1.51      theory(equality) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_2722,plain,
% 6.68/1.51      ( ~ r1_tarski(X0,X1) | r1_tarski(sK1,sK3) | sK3 != X1 | sK1 != X0 ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_1057]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_14621,plain,
% 6.68/1.51      ( ~ r1_tarski(X0,sK3)
% 6.68/1.51      | r1_tarski(sK1,sK3)
% 6.68/1.51      | sK3 != sK3
% 6.68/1.51      | sK1 != X0 ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_2722]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_14623,plain,
% 6.68/1.51      ( r1_tarski(sK1,sK3)
% 6.68/1.51      | ~ r1_tarski(k1_xboole_0,sK3)
% 6.68/1.51      | sK3 != sK3
% 6.68/1.51      | sK1 != k1_xboole_0 ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_14621]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_2395,plain,
% 6.68/1.51      ( ~ r1_tarski(X0,X1)
% 6.68/1.51      | r1_tarski(sK3,k1_xboole_0)
% 6.68/1.51      | sK3 != X0
% 6.68/1.51      | k1_xboole_0 != X1 ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_1057]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_6686,plain,
% 6.68/1.51      ( ~ r1_tarski(sK3,X0)
% 6.68/1.51      | r1_tarski(sK3,k1_xboole_0)
% 6.68/1.51      | sK3 != sK3
% 6.68/1.51      | k1_xboole_0 != X0 ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_2395]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_13331,plain,
% 6.68/1.51      ( ~ r1_tarski(sK3,sK1)
% 6.68/1.51      | r1_tarski(sK3,k1_xboole_0)
% 6.68/1.51      | sK3 != sK3
% 6.68/1.51      | k1_xboole_0 != sK1 ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_6686]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_3,plain,
% 6.68/1.51      ( v1_xboole_0(k1_xboole_0) ),
% 6.68/1.51      inference(cnf_transformation,[],[f56]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_13,plain,
% 6.68/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 6.68/1.51      | ~ r2_hidden(X2,X0)
% 6.68/1.51      | ~ v1_xboole_0(X1) ),
% 6.68/1.51      inference(cnf_transformation,[],[f66]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_11,plain,
% 6.68/1.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 6.68/1.51      inference(cnf_transformation,[],[f65]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_271,plain,
% 6.68/1.51      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 6.68/1.51      inference(prop_impl,[status(thm)],[c_11]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_272,plain,
% 6.68/1.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 6.68/1.51      inference(renaming,[status(thm)],[c_271]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_337,plain,
% 6.68/1.51      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | ~ v1_xboole_0(X2) ),
% 6.68/1.51      inference(bin_hyper_res,[status(thm)],[c_13,c_272]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_454,plain,
% 6.68/1.51      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | k1_xboole_0 != X2 ),
% 6.68/1.51      inference(resolution_lifted,[status(thm)],[c_3,c_337]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_455,plain,
% 6.68/1.51      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,k1_xboole_0) ),
% 6.68/1.51      inference(unflattening,[status(thm)],[c_454]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_12317,plain,
% 6.68/1.51      ( ~ r2_hidden(sK0(sK4,k7_relat_1(sK4,X0)),sK4)
% 6.68/1.51      | ~ r1_tarski(sK4,k1_xboole_0) ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_455]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_12318,plain,
% 6.68/1.51      ( r2_hidden(sK0(sK4,k7_relat_1(sK4,X0)),sK4) != iProver_top
% 6.68/1.51      | r1_tarski(sK4,k1_xboole_0) != iProver_top ),
% 6.68/1.51      inference(predicate_to_equality,[status(thm)],[c_12317]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_12320,plain,
% 6.68/1.51      ( r2_hidden(sK0(sK4,k7_relat_1(sK4,k1_xboole_0)),sK4) != iProver_top
% 6.68/1.51      | r1_tarski(sK4,k1_xboole_0) != iProver_top ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_12318]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_1056,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_3042,plain,
% 6.68/1.51      ( X0 != X1
% 6.68/1.51      | X0 = k2_partfun1(sK1,sK2,sK4,X2)
% 6.68/1.51      | k2_partfun1(sK1,sK2,sK4,X2) != X1 ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_1056]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_7294,plain,
% 6.68/1.51      ( X0 = k2_partfun1(sK1,sK2,sK4,X1)
% 6.68/1.51      | X0 != k7_relat_1(sK4,X1)
% 6.68/1.51      | k2_partfun1(sK1,sK2,sK4,X1) != k7_relat_1(sK4,X1) ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_3042]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_10118,plain,
% 6.68/1.51      ( k2_partfun1(sK1,sK2,sK4,X0) != k7_relat_1(sK4,X0)
% 6.68/1.51      | sK4 = k2_partfun1(sK1,sK2,sK4,X0)
% 6.68/1.51      | sK4 != k7_relat_1(sK4,X0) ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_7294]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_10119,plain,
% 6.68/1.51      ( k2_partfun1(sK1,sK2,sK4,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0)
% 6.68/1.51      | sK4 = k2_partfun1(sK1,sK2,sK4,k1_xboole_0)
% 6.68/1.51      | sK4 != k7_relat_1(sK4,k1_xboole_0) ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_10118]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_7,plain,
% 6.68/1.51      ( r1_tarski(k1_xboole_0,X0) ),
% 6.68/1.51      inference(cnf_transformation,[],[f60]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_2307,plain,
% 6.68/1.51      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_7]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_9443,plain,
% 6.68/1.51      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(sK3,sK2)) ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_2307]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_2279,plain,
% 6.68/1.51      ( X0 != X1 | X0 = sK4 | sK4 != X1 ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_1056]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_4758,plain,
% 6.68/1.51      ( k2_partfun1(sK1,sK2,sK4,sK3) != X0
% 6.68/1.51      | k2_partfun1(sK1,sK2,sK4,sK3) = sK4
% 6.68/1.51      | sK4 != X0 ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_2279]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_8937,plain,
% 6.68/1.51      ( k2_partfun1(sK1,sK2,sK4,sK3) != k2_partfun1(sK1,sK2,sK4,X0)
% 6.68/1.51      | k2_partfun1(sK1,sK2,sK4,sK3) = sK4
% 6.68/1.51      | sK4 != k2_partfun1(sK1,sK2,sK4,X0) ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_4758]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_8940,plain,
% 6.68/1.51      ( k2_partfun1(sK1,sK2,sK4,sK3) != k2_partfun1(sK1,sK2,sK4,k1_xboole_0)
% 6.68/1.51      | k2_partfun1(sK1,sK2,sK4,sK3) = sK4
% 6.68/1.51      | sK4 != k2_partfun1(sK1,sK2,sK4,k1_xboole_0) ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_8937]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_4,plain,
% 6.68/1.51      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 6.68/1.51      inference(cnf_transformation,[],[f59]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_2689,plain,
% 6.68/1.51      ( ~ r1_tarski(X0,sK4) | ~ r1_tarski(sK4,X0) | sK4 = X0 ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_4]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_8807,plain,
% 6.68/1.51      ( ~ r1_tarski(k7_relat_1(sK4,X0),sK4)
% 6.68/1.51      | ~ r1_tarski(sK4,k7_relat_1(sK4,X0))
% 6.68/1.51      | sK4 = k7_relat_1(sK4,X0) ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_2689]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_8808,plain,
% 6.68/1.51      ( sK4 = k7_relat_1(sK4,X0)
% 6.68/1.51      | r1_tarski(k7_relat_1(sK4,X0),sK4) != iProver_top
% 6.68/1.51      | r1_tarski(sK4,k7_relat_1(sK4,X0)) != iProver_top ),
% 6.68/1.51      inference(predicate_to_equality,[status(thm)],[c_8807]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_8810,plain,
% 6.68/1.51      ( sK4 = k7_relat_1(sK4,k1_xboole_0)
% 6.68/1.51      | r1_tarski(k7_relat_1(sK4,k1_xboole_0),sK4) != iProver_top
% 6.68/1.51      | r1_tarski(sK4,k7_relat_1(sK4,k1_xboole_0)) != iProver_top ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_8808]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_7778,plain,
% 6.68/1.51      ( X0 != X1 | X0 = sK2 | sK2 != X1 ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_1056]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_7779,plain,
% 6.68/1.51      ( sK2 != k1_xboole_0
% 6.68/1.51      | k1_xboole_0 = sK2
% 6.68/1.51      | k1_xboole_0 != k1_xboole_0 ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_7778]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_1061,plain,
% 6.68/1.51      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 6.68/1.51      theory(equality) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_2221,plain,
% 6.68/1.51      ( m1_subset_1(X0,X1)
% 6.68/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 6.68/1.51      | X0 != X2
% 6.68/1.51      | X1 != k1_zfmisc_1(X3) ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_1061]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_2868,plain,
% 6.68/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 6.68/1.51      | m1_subset_1(X2,k1_zfmisc_1(X1))
% 6.68/1.51      | X2 != X0
% 6.68/1.51      | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_2221]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_3949,plain,
% 6.68/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.68/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.68/1.51      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 6.68/1.51      | sK4 != X0 ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_2868]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_5291,plain,
% 6.68/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 6.68/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 6.68/1.51      | k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))
% 6.68/1.51      | sK4 != X0 ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_3949]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_5295,plain,
% 6.68/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 6.68/1.51      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 6.68/1.51      | k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))
% 6.68/1.51      | sK4 != k1_xboole_0 ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_5291]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_3930,plain,
% 6.68/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 6.68/1.51      | m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 6.68/1.51      | k2_partfun1(sK1,sK2,sK4,sK3) != X0
% 6.68/1.51      | k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)) ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_2868]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_5290,plain,
% 6.68/1.51      ( m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 6.68/1.51      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 6.68/1.51      | k2_partfun1(sK1,sK2,sK4,sK3) != sK4
% 6.68/1.51      | k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)) ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_3930]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_2148,plain,
% 6.68/1.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.68/1.51      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_11]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_5265,plain,
% 6.68/1.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 6.68/1.51      | ~ r1_tarski(X0,k2_zfmisc_1(sK3,sK2)) ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_2148]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_5267,plain,
% 6.68/1.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 6.68/1.51      | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(sK3,sK2)) ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_5265]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_1,plain,
% 6.68/1.51      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 6.68/1.51      inference(cnf_transformation,[],[f54]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_3329,plain,
% 6.68/1.51      ( r2_hidden(sK0(sK4,X0),sK4) | r1_tarski(sK4,X0) ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_1]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_4718,plain,
% 6.68/1.51      ( r2_hidden(sK0(sK4,k7_relat_1(sK4,X0)),sK4)
% 6.68/1.51      | r1_tarski(sK4,k7_relat_1(sK4,X0)) ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_3329]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_4719,plain,
% 6.68/1.51      ( r2_hidden(sK0(sK4,k7_relat_1(sK4,X0)),sK4) = iProver_top
% 6.68/1.51      | r1_tarski(sK4,k7_relat_1(sK4,X0)) = iProver_top ),
% 6.68/1.51      inference(predicate_to_equality,[status(thm)],[c_4718]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_4721,plain,
% 6.68/1.51      ( r2_hidden(sK0(sK4,k7_relat_1(sK4,k1_xboole_0)),sK4) = iProver_top
% 6.68/1.51      | r1_tarski(sK4,k7_relat_1(sK4,k1_xboole_0)) = iProver_top ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_4719]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_1055,plain,( X0 = X0 ),theory(equality) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_2869,plain,
% 6.68/1.51      ( k1_zfmisc_1(X0) = k1_zfmisc_1(X0) ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_1055]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_4255,plain,
% 6.68/1.51      ( k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)) = k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)) ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_2869]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_1852,plain,
% 6.68/1.51      ( X0 = X1
% 6.68/1.51      | r1_tarski(X1,X0) != iProver_top
% 6.68/1.51      | r1_tarski(X0,X1) != iProver_top ),
% 6.68/1.51      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_3887,plain,
% 6.68/1.51      ( sK3 = sK1 | r1_tarski(sK1,sK3) != iProver_top ),
% 6.68/1.51      inference(superposition,[status(thm)],[c_1836,c_1852]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_3916,plain,
% 6.68/1.51      ( ~ r1_tarski(sK1,sK3) | sK3 = sK1 ),
% 6.68/1.51      inference(predicate_to_equality_rev,[status(thm)],[c_3887]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_3330,plain,
% 6.68/1.51      ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0)) | r1_tarski(sK4,X0) ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_12]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_3331,plain,
% 6.68/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 6.68/1.51      | r1_tarski(sK4,X0) = iProver_top ),
% 6.68/1.51      inference(predicate_to_equality,[status(thm)],[c_3330]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_3333,plain,
% 6.68/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 6.68/1.51      | r1_tarski(sK4,k1_xboole_0) = iProver_top ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_3331]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_2749,plain,
% 6.68/1.51      ( r1_tarski(k1_xboole_0,sK3) ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_7]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_2690,plain,
% 6.68/1.51      ( sK4 = X0
% 6.68/1.51      | r1_tarski(X0,sK4) != iProver_top
% 6.68/1.51      | r1_tarski(sK4,X0) != iProver_top ),
% 6.68/1.51      inference(predicate_to_equality,[status(thm)],[c_2689]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_2692,plain,
% 6.68/1.51      ( sK4 = k1_xboole_0
% 6.68/1.51      | r1_tarski(sK4,k1_xboole_0) != iProver_top
% 6.68/1.51      | r1_tarski(k1_xboole_0,sK4) != iProver_top ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_2690]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_2661,plain,
% 6.68/1.51      ( r1_tarski(k1_xboole_0,sK4) ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_7]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_2664,plain,
% 6.68/1.51      ( r1_tarski(k1_xboole_0,sK4) = iProver_top ),
% 6.68/1.51      inference(predicate_to_equality,[status(thm)],[c_2661]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_6,plain,
% 6.68/1.51      ( r1_tarski(X0,X0) ),
% 6.68/1.51      inference(cnf_transformation,[],[f93]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_2655,plain,
% 6.68/1.51      ( r1_tarski(sK4,sK4) ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_6]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_2263,plain,
% 6.68/1.51      ( ~ r1_tarski(X0,sK4) | ~ r1_tarski(sK4,X0) | X0 = sK4 ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_4]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_2654,plain,
% 6.68/1.51      ( ~ r1_tarski(sK4,sK4) | sK4 = sK4 ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_2263]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_2561,plain,
% 6.68/1.51      ( sK1 = sK1 ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_1055]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_2182,plain,
% 6.68/1.51      ( sK1 != X0 | sK1 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_1056]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_2560,plain,
% 6.68/1.51      ( sK1 != sK1 | sK1 = k1_xboole_0 | k1_xboole_0 != sK1 ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_2182]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_2555,plain,
% 6.68/1.51      ( sK3 = sK3 ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_1055]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_2549,plain,
% 6.68/1.51      ( sK2 = sK2 ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_1055]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_2211,plain,
% 6.68/1.51      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 6.68/1.51      | v1_funct_1(k2_partfun1(X0,X1,sK4,X2))
% 6.68/1.51      | ~ v1_funct_1(sK4) ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_28]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_2355,plain,
% 6.68/1.51      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 6.68/1.51      | v1_funct_1(k2_partfun1(sK1,sK2,sK4,X0))
% 6.68/1.51      | ~ v1_funct_1(sK4) ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_2211]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_2463,plain,
% 6.68/1.51      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 6.68/1.51      | v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))
% 6.68/1.51      | ~ v1_funct_1(sK4) ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_2355]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_2363,plain,
% 6.68/1.51      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 6.68/1.51      | ~ v1_funct_1(sK4)
% 6.68/1.51      | k2_partfun1(sK1,sK2,sK4,k1_xboole_0) = k7_relat_1(sK4,k1_xboole_0) ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_2361]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_15,plain,
% 6.68/1.51      ( r1_tarski(k7_relat_1(X0,X1),X0) | ~ v1_relat_1(X0) ),
% 6.68/1.51      inference(cnf_transformation,[],[f68]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_2245,plain,
% 6.68/1.51      ( r1_tarski(k7_relat_1(sK4,X0),sK4) | ~ v1_relat_1(sK4) ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_15]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_2246,plain,
% 6.68/1.51      ( r1_tarski(k7_relat_1(sK4,X0),sK4) = iProver_top
% 6.68/1.51      | v1_relat_1(sK4) != iProver_top ),
% 6.68/1.51      inference(predicate_to_equality,[status(thm)],[c_2245]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_2248,plain,
% 6.68/1.51      ( r1_tarski(k7_relat_1(sK4,k1_xboole_0),sK4) = iProver_top
% 6.68/1.51      | v1_relat_1(sK4) != iProver_top ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_2246]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_2171,plain,
% 6.68/1.51      ( ~ r1_tarski(sK3,k1_xboole_0)
% 6.68/1.51      | ~ r1_tarski(k1_xboole_0,sK3)
% 6.68/1.51      | sK3 = k1_xboole_0 ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_4]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_680,plain,
% 6.68/1.51      ( ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 6.68/1.51      | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))
% 6.68/1.51      | k2_partfun1(sK1,sK2,sK4,sK3) != sK4
% 6.68/1.51      | sK3 != sK1
% 6.68/1.51      | sK2 != sK2 ),
% 6.68/1.51      inference(resolution_lifted,[status(thm)],[c_33,c_37]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_109,plain,
% 6.68/1.51      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_9]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_10,plain,
% 6.68/1.51      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 6.68/1.51      | k1_xboole_0 = X1
% 6.68/1.51      | k1_xboole_0 = X0 ),
% 6.68/1.51      inference(cnf_transformation,[],[f61]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(c_108,plain,
% 6.68/1.51      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 6.68/1.51      | k1_xboole_0 = k1_xboole_0 ),
% 6.68/1.51      inference(instantiation,[status(thm)],[c_10]) ).
% 6.68/1.51  
% 6.68/1.51  cnf(contradiction,plain,
% 6.68/1.51      ( $false ),
% 6.68/1.51      inference(minisat,
% 6.68/1.51                [status(thm)],
% 6.68/1.51                [c_21171,c_20925,c_16901,c_14623,c_13331,c_12320,c_10119,
% 6.68/1.51                 c_9443,c_8940,c_8810,c_7779,c_5295,c_5290,c_5267,c_4721,
% 6.68/1.51                 c_4255,c_3916,c_3333,c_2749,c_2692,c_2664,c_2655,c_2654,
% 6.68/1.51                 c_2561,c_2560,c_2555,c_2549,c_2463,c_2363,c_2248,c_2171,
% 6.68/1.51                 c_2154,c_680,c_109,c_108,c_34,c_35,c_41,c_36,c_38]) ).
% 6.68/1.51  
% 6.68/1.51  
% 6.68/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 6.68/1.51  
% 6.68/1.51  ------                               Statistics
% 6.68/1.51  
% 6.68/1.51  ------ General
% 6.68/1.51  
% 6.68/1.51  abstr_ref_over_cycles:                  0
% 6.68/1.51  abstr_ref_under_cycles:                 0
% 6.68/1.51  gc_basic_clause_elim:                   0
% 6.68/1.51  forced_gc_time:                         0
% 6.68/1.51  parsing_time:                           0.012
% 6.68/1.51  unif_index_cands_time:                  0.
% 6.68/1.51  unif_index_add_time:                    0.
% 6.68/1.51  orderings_time:                         0.
% 6.68/1.51  out_proof_time:                         0.013
% 6.68/1.51  total_time:                             0.543
% 6.68/1.51  num_of_symbols:                         52
% 6.68/1.51  num_of_terms:                           20167
% 6.68/1.51  
% 6.68/1.51  ------ Preprocessing
% 6.68/1.51  
% 6.68/1.51  num_of_splits:                          0
% 6.68/1.51  num_of_split_atoms:                     0
% 6.68/1.51  num_of_reused_defs:                     0
% 6.68/1.51  num_eq_ax_congr_red:                    27
% 6.68/1.51  num_of_sem_filtered_clauses:            1
% 6.68/1.51  num_of_subtypes:                        0
% 6.68/1.51  monotx_restored_types:                  0
% 6.68/1.51  sat_num_of_epr_types:                   0
% 6.68/1.51  sat_num_of_non_cyclic_types:            0
% 6.68/1.51  sat_guarded_non_collapsed_types:        0
% 6.68/1.51  num_pure_diseq_elim:                    0
% 6.68/1.51  simp_replaced_by:                       0
% 6.68/1.51  res_preprocessed:                       178
% 6.68/1.51  prep_upred:                             0
% 6.68/1.51  prep_unflattend:                        44
% 6.68/1.51  smt_new_axioms:                         0
% 6.68/1.51  pred_elim_cands:                        5
% 6.68/1.51  pred_elim:                              2
% 6.68/1.51  pred_elim_cl:                           -1
% 6.68/1.51  pred_elim_cycles:                       4
% 6.68/1.51  merged_defs:                            8
% 6.68/1.51  merged_defs_ncl:                        0
% 6.68/1.51  bin_hyper_res:                          9
% 6.68/1.51  prep_cycles:                            4
% 6.68/1.51  pred_elim_time:                         0.009
% 6.68/1.51  splitting_time:                         0.
% 6.68/1.51  sem_filter_time:                        0.
% 6.68/1.51  monotx_time:                            0.
% 6.68/1.51  subtype_inf_time:                       0.
% 6.68/1.51  
% 6.68/1.51  ------ Problem properties
% 6.68/1.51  
% 6.68/1.51  clauses:                                38
% 6.68/1.51  conjectures:                            4
% 6.68/1.51  epr:                                    8
% 6.68/1.51  horn:                                   32
% 6.68/1.51  ground:                                 12
% 6.68/1.51  unary:                                  7
% 6.68/1.51  binary:                                 13
% 6.68/1.51  lits:                                   103
% 6.68/1.51  lits_eq:                                35
% 6.68/1.51  fd_pure:                                0
% 6.68/1.51  fd_pseudo:                              0
% 6.68/1.51  fd_cond:                                3
% 6.68/1.51  fd_pseudo_cond:                         1
% 6.68/1.51  ac_symbols:                             0
% 6.68/1.51  
% 6.68/1.51  ------ Propositional Solver
% 6.68/1.51  
% 6.68/1.51  prop_solver_calls:                      31
% 6.68/1.51  prop_fast_solver_calls:                 1892
% 6.68/1.51  smt_solver_calls:                       0
% 6.68/1.51  smt_fast_solver_calls:                  0
% 6.68/1.51  prop_num_of_clauses:                    7945
% 6.68/1.51  prop_preprocess_simplified:             15507
% 6.68/1.51  prop_fo_subsumed:                       45
% 6.68/1.51  prop_solver_time:                       0.
% 6.68/1.51  smt_solver_time:                        0.
% 6.68/1.51  smt_fast_solver_time:                   0.
% 6.68/1.51  prop_fast_solver_time:                  0.
% 6.68/1.51  prop_unsat_core_time:                   0.
% 6.68/1.51  
% 6.68/1.51  ------ QBF
% 6.68/1.51  
% 6.68/1.51  qbf_q_res:                              0
% 6.68/1.51  qbf_num_tautologies:                    0
% 6.68/1.51  qbf_prep_cycles:                        0
% 6.68/1.51  
% 6.68/1.51  ------ BMC1
% 6.68/1.51  
% 6.68/1.51  bmc1_current_bound:                     -1
% 6.68/1.51  bmc1_last_solved_bound:                 -1
% 6.68/1.51  bmc1_unsat_core_size:                   -1
% 6.68/1.51  bmc1_unsat_core_parents_size:           -1
% 6.68/1.51  bmc1_merge_next_fun:                    0
% 6.68/1.51  bmc1_unsat_core_clauses_time:           0.
% 6.68/1.51  
% 6.68/1.51  ------ Instantiation
% 6.68/1.51  
% 6.68/1.51  inst_num_of_clauses:                    2079
% 6.68/1.51  inst_num_in_passive:                    920
% 6.68/1.51  inst_num_in_active:                     858
% 6.68/1.51  inst_num_in_unprocessed:                301
% 6.68/1.51  inst_num_of_loops:                      1210
% 6.68/1.51  inst_num_of_learning_restarts:          0
% 6.68/1.51  inst_num_moves_active_passive:          348
% 6.68/1.51  inst_lit_activity:                      0
% 6.68/1.51  inst_lit_activity_moves:                0
% 6.68/1.51  inst_num_tautologies:                   0
% 6.68/1.51  inst_num_prop_implied:                  0
% 6.68/1.51  inst_num_existing_simplified:           0
% 6.68/1.51  inst_num_eq_res_simplified:             0
% 6.68/1.51  inst_num_child_elim:                    0
% 6.68/1.51  inst_num_of_dismatching_blockings:      1258
% 6.68/1.51  inst_num_of_non_proper_insts:           2100
% 6.68/1.51  inst_num_of_duplicates:                 0
% 6.68/1.51  inst_inst_num_from_inst_to_res:         0
% 6.68/1.51  inst_dismatching_checking_time:         0.
% 6.68/1.51  
% 6.68/1.51  ------ Resolution
% 6.68/1.51  
% 6.68/1.51  res_num_of_clauses:                     0
% 6.68/1.51  res_num_in_passive:                     0
% 6.68/1.51  res_num_in_active:                      0
% 6.68/1.51  res_num_of_loops:                       182
% 6.68/1.51  res_forward_subset_subsumed:            76
% 6.68/1.51  res_backward_subset_subsumed:           0
% 6.68/1.51  res_forward_subsumed:                   0
% 6.68/1.51  res_backward_subsumed:                  0
% 6.68/1.51  res_forward_subsumption_resolution:     3
% 6.68/1.51  res_backward_subsumption_resolution:    0
% 6.68/1.51  res_clause_to_clause_subsumption:       3415
% 6.68/1.51  res_orphan_elimination:                 0
% 6.68/1.51  res_tautology_del:                      125
% 6.68/1.51  res_num_eq_res_simplified:              1
% 6.68/1.51  res_num_sel_changes:                    0
% 6.68/1.51  res_moves_from_active_to_pass:          0
% 6.68/1.51  
% 6.68/1.51  ------ Superposition
% 6.68/1.51  
% 6.68/1.51  sup_time_total:                         0.
% 6.68/1.51  sup_time_generating:                    0.
% 6.68/1.51  sup_time_sim_full:                      0.
% 6.68/1.51  sup_time_sim_immed:                     0.
% 6.68/1.51  
% 6.68/1.51  sup_num_of_clauses:                     454
% 6.68/1.51  sup_num_in_active:                      128
% 6.68/1.51  sup_num_in_passive:                     326
% 6.68/1.51  sup_num_of_loops:                       240
% 6.68/1.51  sup_fw_superposition:                   480
% 6.68/1.51  sup_bw_superposition:                   239
% 6.68/1.51  sup_immediate_simplified:               126
% 6.68/1.51  sup_given_eliminated:                   3
% 6.68/1.51  comparisons_done:                       0
% 6.68/1.51  comparisons_avoided:                    187
% 6.68/1.51  
% 6.68/1.51  ------ Simplifications
% 6.68/1.51  
% 6.68/1.51  
% 6.68/1.51  sim_fw_subset_subsumed:                 26
% 6.68/1.51  sim_bw_subset_subsumed:                 52
% 6.68/1.51  sim_fw_subsumed:                        11
% 6.68/1.51  sim_bw_subsumed:                        4
% 6.68/1.51  sim_fw_subsumption_res:                 37
% 6.68/1.51  sim_bw_subsumption_res:                 4
% 6.68/1.51  sim_tautology_del:                      6
% 6.68/1.51  sim_eq_tautology_del:                   53
% 6.68/1.51  sim_eq_res_simp:                        4
% 6.68/1.51  sim_fw_demodulated:                     72
% 6.68/1.51  sim_bw_demodulated:                     86
% 6.68/1.51  sim_light_normalised:                   31
% 6.68/1.51  sim_joinable_taut:                      0
% 6.68/1.51  sim_joinable_simp:                      0
% 6.68/1.51  sim_ac_normalised:                      0
% 6.68/1.51  sim_smt_subsumption:                    0
% 6.68/1.51  
%------------------------------------------------------------------------------
