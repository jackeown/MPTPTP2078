%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:52 EST 2020

% Result     : Theorem 3.40s
% Output     : CNFRefutation 3.40s
% Verified   : 
% Statistics : Number of formulae       :  240 (4790 expanded)
%              Number of clauses        :  157 (1584 expanded)
%              Number of leaves         :   21 ( 896 expanded)
%              Depth                    :   26
%              Number of atoms          :  725 (26331 expanded)
%              Number of equality atoms :  377 (7157 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f49,plain,
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

fof(f50,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f41,f49])).

fof(f85,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

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
    inference(flattening,[],[f32])).

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
    inference(nnf_transformation,[],[f33])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f83,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f84,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f50])).

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

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

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

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f82,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f87,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f50])).

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

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

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

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f86,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f50])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f44])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f91,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f92,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f75])).

fof(f93,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f92])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f90,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f58])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f53,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f95,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f73])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f64,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
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

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f96,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f71])).

cnf(c_33,negated_conjecture,
    ( r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1717,plain,
    ( r1_tarski(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_631,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_35])).

cnf(c_632,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_631])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_634,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_632,c_34])).

cnf(c_1716,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1722,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3736,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1716,c_1722])).

cnf(c_3883,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_634,c_3736])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1725,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_5007,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3883,c_1725])).

cnf(c_39,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2008,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2009,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2008])).

cnf(c_5514,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | sK1 = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5007,c_39,c_2009])).

cnf(c_5515,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5514])).

cnf(c_5525,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1717,c_5515])).

cnf(c_28,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1718,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_6194,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5525,c_1718])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1719,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_5927,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1716,c_1719])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2082,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_2196,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_2082])).

cnf(c_6134,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5927,c_36,c_34,c_2196])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1720,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_5693,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1716,c_1720])).

cnf(c_37,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_2058,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_2164,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2058])).

cnf(c_2165,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2164])).

cnf(c_5974,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5693,c_37,c_39,c_2165])).

cnf(c_6143,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6134,c_5974])).

cnf(c_8236,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6194,c_6143])).

cnf(c_29,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_31,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_642,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(X0)
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relat_1(X0) != sK2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_31])).

cnf(c_643,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
    inference(unflattening,[status(thm)],[c_642])).

cnf(c_17,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_11,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_430,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_17,c_11])).

cnf(c_434,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_430,c_16])).

cnf(c_435,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_434])).

cnf(c_655,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_643,c_16,c_435])).

cnf(c_1705,plain,
    ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_655])).

cnf(c_6141,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6134,c_1705])).

cnf(c_6157,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6141,c_6143])).

cnf(c_10154,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5525,c_6157])).

cnf(c_10231,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8236,c_10154])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1721,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_7087,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6134,c_1721])).

cnf(c_7909,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7087,c_37,c_39])).

cnf(c_1723,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_7922,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7909,c_1723])).

cnf(c_1714,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_435])).

cnf(c_7921,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_7909,c_1714])).

cnf(c_14344,plain,
    ( sK1 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_10231,c_7922,c_7921])).

cnf(c_14372,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_14344,c_7909])).

cnf(c_32,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_14389,plain,
    ( sK0 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_14344,c_32])).

cnf(c_14390,plain,
    ( sK0 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_14389])).

cnf(c_14447,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14372,c_14390])).

cnf(c_6,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_14449,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_14447,c_6])).

cnf(c_19,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_459,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 != X0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_31])).

cnf(c_460,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_459])).

cnf(c_1713,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_460])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1905,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1713,c_5])).

cnf(c_8,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_106,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_108,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_106])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_111,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_113,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_111])).

cnf(c_2282,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2164])).

cnf(c_2283,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2282])).

cnf(c_2346,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1905,c_37,c_39,c_108,c_113,c_2283])).

cnf(c_6139,plain,
    ( k7_relat_1(sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6134,c_2346])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_109,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_110,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_112,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2030,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK2)
    | sK2 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1009,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2303,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK0,k1_xboole_0)
    | sK0 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_1009])).

cnf(c_2305,plain,
    ( r1_tarski(sK0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | sK0 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2303])).

cnf(c_1008,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2046,plain,
    ( sK0 != X0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1008])).

cnf(c_2385,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2046])).

cnf(c_1007,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2386,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1007])).

cnf(c_3042,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1008])).

cnf(c_3043,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3042])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2289,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3188,plain,
    ( ~ r1_tarski(sK2,sK0)
    | r1_tarski(sK2,k1_xboole_0)
    | ~ r1_tarski(sK0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2289])).

cnf(c_3958,plain,
    ( r1_tarski(k1_xboole_0,sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_6409,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6139,c_33,c_32,c_109,c_110,c_112,c_2030,c_2305,c_2385,c_2386,c_3043,c_3188,c_3958,c_5525,c_6157])).

cnf(c_14375,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14344,c_6409])).

cnf(c_14438,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14375,c_5])).

cnf(c_14451,plain,
    ( sK2 = k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_14449,c_14438])).

cnf(c_21,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_556,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | sK2 != k1_xboole_0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_31])).

cnf(c_557,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_556])).

cnf(c_1709,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_557])).

cnf(c_1918,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1709,c_6])).

cnf(c_2407,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | sK2 != k1_xboole_0
    | k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1918,c_37,c_39,c_2283])).

cnf(c_2408,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2407])).

cnf(c_6138,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6134,c_2408])).

cnf(c_6712,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,sK2)) != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6138,c_6409])).

cnf(c_14374,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14344,c_6712])).

cnf(c_14444,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14374,c_5])).

cnf(c_14452,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_14449,c_14444])).

cnf(c_14456,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_14451,c_14452])).

cnf(c_2937,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1716,c_1723])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1726,plain,
    ( k7_relat_1(X0,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3028,plain,
    ( k7_relat_1(sK3,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2937,c_1726])).

cnf(c_14459,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_14456,c_3028])).

cnf(c_1730,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5006,plain,
    ( k1_relat_1(k7_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1730,c_1725])).

cnf(c_9850,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7922,c_5006])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1727,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2615,plain,
    ( k7_relat_1(k7_relat_1(X0,X1),k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1727,c_1726])).

cnf(c_3275,plain,
    ( k7_relat_1(k7_relat_1(sK3,X0),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2937,c_2615])).

cnf(c_9852,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_9850,c_3275])).

cnf(c_6406,plain,
    ( v1_funct_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3028,c_6143])).

cnf(c_2153,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2156,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2153])).

cnf(c_2158,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2156])).

cnf(c_2003,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2004,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2003])).

cnf(c_2006,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
    | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2004])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_531,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ r1_tarski(k2_relat_1(X2),X3)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | X2 != X0
    | X3 != X1
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | k1_relat_1(X2) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_29])).

cnf(c_532,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_531])).

cnf(c_533,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
    | r1_tarski(k2_relat_1(X1),X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_532])).

cnf(c_535,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_533])).

cnf(c_436,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_435])).

cnf(c_438,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_436])).

cnf(c_82,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_84,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_82])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14459,c_9852,c_6406,c_2158,c_2006,c_535,c_438,c_84])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.32  % Computer   : n021.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 15:43:34 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.32  % Running in FOF mode
% 3.40/0.96  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.40/0.96  
% 3.40/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.40/0.96  
% 3.40/0.96  ------  iProver source info
% 3.40/0.96  
% 3.40/0.96  git: date: 2020-06-30 10:37:57 +0100
% 3.40/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.40/0.96  git: non_committed_changes: false
% 3.40/0.96  git: last_make_outside_of_git: false
% 3.40/0.96  
% 3.40/0.96  ------ 
% 3.40/0.96  
% 3.40/0.96  ------ Input Options
% 3.40/0.96  
% 3.40/0.96  --out_options                           all
% 3.40/0.96  --tptp_safe_out                         true
% 3.40/0.96  --problem_path                          ""
% 3.40/0.96  --include_path                          ""
% 3.40/0.96  --clausifier                            res/vclausify_rel
% 3.40/0.96  --clausifier_options                    --mode clausify
% 3.40/0.96  --stdin                                 false
% 3.40/0.96  --stats_out                             all
% 3.40/0.96  
% 3.40/0.96  ------ General Options
% 3.40/0.96  
% 3.40/0.96  --fof                                   false
% 3.40/0.96  --time_out_real                         305.
% 3.40/0.96  --time_out_virtual                      -1.
% 3.40/0.96  --symbol_type_check                     false
% 3.40/0.96  --clausify_out                          false
% 3.40/0.96  --sig_cnt_out                           false
% 3.40/0.96  --trig_cnt_out                          false
% 3.40/0.96  --trig_cnt_out_tolerance                1.
% 3.40/0.96  --trig_cnt_out_sk_spl                   false
% 3.40/0.96  --abstr_cl_out                          false
% 3.40/0.96  
% 3.40/0.96  ------ Global Options
% 3.40/0.96  
% 3.40/0.96  --schedule                              default
% 3.40/0.96  --add_important_lit                     false
% 3.40/0.96  --prop_solver_per_cl                    1000
% 3.40/0.96  --min_unsat_core                        false
% 3.40/0.96  --soft_assumptions                      false
% 3.40/0.96  --soft_lemma_size                       3
% 3.40/0.96  --prop_impl_unit_size                   0
% 3.40/0.96  --prop_impl_unit                        []
% 3.40/0.96  --share_sel_clauses                     true
% 3.40/0.96  --reset_solvers                         false
% 3.40/0.96  --bc_imp_inh                            [conj_cone]
% 3.40/0.96  --conj_cone_tolerance                   3.
% 3.40/0.96  --extra_neg_conj                        none
% 3.40/0.96  --large_theory_mode                     true
% 3.40/0.96  --prolific_symb_bound                   200
% 3.40/0.96  --lt_threshold                          2000
% 3.40/0.96  --clause_weak_htbl                      true
% 3.40/0.96  --gc_record_bc_elim                     false
% 3.40/0.96  
% 3.40/0.96  ------ Preprocessing Options
% 3.40/0.96  
% 3.40/0.96  --preprocessing_flag                    true
% 3.40/0.96  --time_out_prep_mult                    0.1
% 3.40/0.96  --splitting_mode                        input
% 3.40/0.96  --splitting_grd                         true
% 3.40/0.96  --splitting_cvd                         false
% 3.40/0.96  --splitting_cvd_svl                     false
% 3.40/0.96  --splitting_nvd                         32
% 3.40/0.96  --sub_typing                            true
% 3.40/0.96  --prep_gs_sim                           true
% 3.40/0.96  --prep_unflatten                        true
% 3.40/0.96  --prep_res_sim                          true
% 3.40/0.96  --prep_upred                            true
% 3.40/0.96  --prep_sem_filter                       exhaustive
% 3.40/0.96  --prep_sem_filter_out                   false
% 3.40/0.96  --pred_elim                             true
% 3.40/0.96  --res_sim_input                         true
% 3.40/0.96  --eq_ax_congr_red                       true
% 3.40/0.96  --pure_diseq_elim                       true
% 3.40/0.96  --brand_transform                       false
% 3.40/0.96  --non_eq_to_eq                          false
% 3.40/0.96  --prep_def_merge                        true
% 3.40/0.96  --prep_def_merge_prop_impl              false
% 3.40/0.96  --prep_def_merge_mbd                    true
% 3.40/0.96  --prep_def_merge_tr_red                 false
% 3.40/0.96  --prep_def_merge_tr_cl                  false
% 3.40/0.96  --smt_preprocessing                     true
% 3.40/0.96  --smt_ac_axioms                         fast
% 3.40/0.96  --preprocessed_out                      false
% 3.40/0.96  --preprocessed_stats                    false
% 3.40/0.96  
% 3.40/0.96  ------ Abstraction refinement Options
% 3.40/0.96  
% 3.40/0.96  --abstr_ref                             []
% 3.40/0.96  --abstr_ref_prep                        false
% 3.40/0.96  --abstr_ref_until_sat                   false
% 3.40/0.96  --abstr_ref_sig_restrict                funpre
% 3.40/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 3.40/0.96  --abstr_ref_under                       []
% 3.40/0.96  
% 3.40/0.96  ------ SAT Options
% 3.40/0.96  
% 3.40/0.96  --sat_mode                              false
% 3.40/0.96  --sat_fm_restart_options                ""
% 3.40/0.96  --sat_gr_def                            false
% 3.40/0.96  --sat_epr_types                         true
% 3.40/0.96  --sat_non_cyclic_types                  false
% 3.40/0.96  --sat_finite_models                     false
% 3.40/0.96  --sat_fm_lemmas                         false
% 3.40/0.96  --sat_fm_prep                           false
% 3.40/0.96  --sat_fm_uc_incr                        true
% 3.40/0.96  --sat_out_model                         small
% 3.40/0.96  --sat_out_clauses                       false
% 3.40/0.96  
% 3.40/0.96  ------ QBF Options
% 3.40/0.96  
% 3.40/0.96  --qbf_mode                              false
% 3.40/0.96  --qbf_elim_univ                         false
% 3.40/0.96  --qbf_dom_inst                          none
% 3.40/0.96  --qbf_dom_pre_inst                      false
% 3.40/0.96  --qbf_sk_in                             false
% 3.40/0.96  --qbf_pred_elim                         true
% 3.40/0.96  --qbf_split                             512
% 3.40/0.96  
% 3.40/0.96  ------ BMC1 Options
% 3.40/0.96  
% 3.40/0.96  --bmc1_incremental                      false
% 3.40/0.96  --bmc1_axioms                           reachable_all
% 3.40/0.96  --bmc1_min_bound                        0
% 3.40/0.96  --bmc1_max_bound                        -1
% 3.40/0.96  --bmc1_max_bound_default                -1
% 3.40/0.96  --bmc1_symbol_reachability              true
% 3.40/0.96  --bmc1_property_lemmas                  false
% 3.40/0.96  --bmc1_k_induction                      false
% 3.40/0.96  --bmc1_non_equiv_states                 false
% 3.40/0.96  --bmc1_deadlock                         false
% 3.40/0.96  --bmc1_ucm                              false
% 3.40/0.96  --bmc1_add_unsat_core                   none
% 3.40/0.96  --bmc1_unsat_core_children              false
% 3.40/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 3.40/0.96  --bmc1_out_stat                         full
% 3.40/0.96  --bmc1_ground_init                      false
% 3.40/0.96  --bmc1_pre_inst_next_state              false
% 3.40/0.96  --bmc1_pre_inst_state                   false
% 3.40/0.96  --bmc1_pre_inst_reach_state             false
% 3.40/0.96  --bmc1_out_unsat_core                   false
% 3.40/0.96  --bmc1_aig_witness_out                  false
% 3.40/0.96  --bmc1_verbose                          false
% 3.40/0.96  --bmc1_dump_clauses_tptp                false
% 3.40/0.96  --bmc1_dump_unsat_core_tptp             false
% 3.40/0.96  --bmc1_dump_file                        -
% 3.40/0.96  --bmc1_ucm_expand_uc_limit              128
% 3.40/0.96  --bmc1_ucm_n_expand_iterations          6
% 3.40/0.96  --bmc1_ucm_extend_mode                  1
% 3.40/0.96  --bmc1_ucm_init_mode                    2
% 3.40/0.96  --bmc1_ucm_cone_mode                    none
% 3.40/0.96  --bmc1_ucm_reduced_relation_type        0
% 3.40/0.96  --bmc1_ucm_relax_model                  4
% 3.40/0.96  --bmc1_ucm_full_tr_after_sat            true
% 3.40/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 3.40/0.96  --bmc1_ucm_layered_model                none
% 3.40/0.96  --bmc1_ucm_max_lemma_size               10
% 3.40/0.96  
% 3.40/0.96  ------ AIG Options
% 3.40/0.96  
% 3.40/0.96  --aig_mode                              false
% 3.40/0.96  
% 3.40/0.96  ------ Instantiation Options
% 3.40/0.96  
% 3.40/0.96  --instantiation_flag                    true
% 3.40/0.96  --inst_sos_flag                         false
% 3.40/0.96  --inst_sos_phase                        true
% 3.40/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.40/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.40/0.96  --inst_lit_sel_side                     num_symb
% 3.40/0.96  --inst_solver_per_active                1400
% 3.40/0.96  --inst_solver_calls_frac                1.
% 3.40/0.96  --inst_passive_queue_type               priority_queues
% 3.40/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.40/0.96  --inst_passive_queues_freq              [25;2]
% 3.40/0.96  --inst_dismatching                      true
% 3.40/0.96  --inst_eager_unprocessed_to_passive     true
% 3.40/0.96  --inst_prop_sim_given                   true
% 3.40/0.96  --inst_prop_sim_new                     false
% 3.40/0.96  --inst_subs_new                         false
% 3.40/0.96  --inst_eq_res_simp                      false
% 3.40/0.96  --inst_subs_given                       false
% 3.40/0.96  --inst_orphan_elimination               true
% 3.40/0.96  --inst_learning_loop_flag               true
% 3.40/0.96  --inst_learning_start                   3000
% 3.40/0.96  --inst_learning_factor                  2
% 3.40/0.96  --inst_start_prop_sim_after_learn       3
% 3.40/0.96  --inst_sel_renew                        solver
% 3.40/0.96  --inst_lit_activity_flag                true
% 3.40/0.96  --inst_restr_to_given                   false
% 3.40/0.96  --inst_activity_threshold               500
% 3.40/0.96  --inst_out_proof                        true
% 3.40/0.96  
% 3.40/0.96  ------ Resolution Options
% 3.40/0.96  
% 3.40/0.96  --resolution_flag                       true
% 3.40/0.96  --res_lit_sel                           adaptive
% 3.40/0.96  --res_lit_sel_side                      none
% 3.40/0.96  --res_ordering                          kbo
% 3.40/0.96  --res_to_prop_solver                    active
% 3.40/0.96  --res_prop_simpl_new                    false
% 3.40/0.96  --res_prop_simpl_given                  true
% 3.40/0.96  --res_passive_queue_type                priority_queues
% 3.40/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.40/0.96  --res_passive_queues_freq               [15;5]
% 3.40/0.96  --res_forward_subs                      full
% 3.40/0.96  --res_backward_subs                     full
% 3.40/0.96  --res_forward_subs_resolution           true
% 3.40/0.96  --res_backward_subs_resolution          true
% 3.40/0.96  --res_orphan_elimination                true
% 3.40/0.96  --res_time_limit                        2.
% 3.40/0.96  --res_out_proof                         true
% 3.40/0.96  
% 3.40/0.96  ------ Superposition Options
% 3.40/0.96  
% 3.40/0.96  --superposition_flag                    true
% 3.40/0.96  --sup_passive_queue_type                priority_queues
% 3.40/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.40/0.96  --sup_passive_queues_freq               [8;1;4]
% 3.40/0.96  --demod_completeness_check              fast
% 3.40/0.96  --demod_use_ground                      true
% 3.40/0.96  --sup_to_prop_solver                    passive
% 3.40/0.96  --sup_prop_simpl_new                    true
% 3.40/0.96  --sup_prop_simpl_given                  true
% 3.40/0.96  --sup_fun_splitting                     false
% 3.40/0.96  --sup_smt_interval                      50000
% 3.40/0.96  
% 3.40/0.96  ------ Superposition Simplification Setup
% 3.40/0.96  
% 3.40/0.96  --sup_indices_passive                   []
% 3.40/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.40/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.40/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.40/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 3.40/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.40/0.96  --sup_full_bw                           [BwDemod]
% 3.40/0.96  --sup_immed_triv                        [TrivRules]
% 3.40/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.40/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.40/0.96  --sup_immed_bw_main                     []
% 3.40/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.40/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 3.40/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.40/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.40/0.96  
% 3.40/0.96  ------ Combination Options
% 3.40/0.96  
% 3.40/0.96  --comb_res_mult                         3
% 3.40/0.96  --comb_sup_mult                         2
% 3.40/0.96  --comb_inst_mult                        10
% 3.40/0.96  
% 3.40/0.96  ------ Debug Options
% 3.40/0.96  
% 3.40/0.96  --dbg_backtrace                         false
% 3.40/0.96  --dbg_dump_prop_clauses                 false
% 3.40/0.96  --dbg_dump_prop_clauses_file            -
% 3.40/0.96  --dbg_out_stat                          false
% 3.40/0.96  ------ Parsing...
% 3.40/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.40/0.96  
% 3.40/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.40/0.96  
% 3.40/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.40/0.96  
% 3.40/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.40/0.96  ------ Proving...
% 3.40/0.96  ------ Problem Properties 
% 3.40/0.96  
% 3.40/0.96  
% 3.40/0.96  clauses                                 35
% 3.40/0.96  conjectures                             4
% 3.40/0.96  EPR                                     7
% 3.40/0.96  Horn                                    30
% 3.40/0.96  unary                                   7
% 3.40/0.96  binary                                  10
% 3.40/0.96  lits                                    95
% 3.40/0.96  lits eq                                 35
% 3.40/0.96  fd_pure                                 0
% 3.40/0.96  fd_pseudo                               0
% 3.40/0.96  fd_cond                                 3
% 3.40/0.96  fd_pseudo_cond                          1
% 3.40/0.96  AC symbols                              0
% 3.40/0.96  
% 3.40/0.96  ------ Schedule dynamic 5 is on 
% 3.40/0.96  
% 3.40/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.40/0.96  
% 3.40/0.96  
% 3.40/0.96  ------ 
% 3.40/0.96  Current options:
% 3.40/0.96  ------ 
% 3.40/0.96  
% 3.40/0.96  ------ Input Options
% 3.40/0.96  
% 3.40/0.96  --out_options                           all
% 3.40/0.96  --tptp_safe_out                         true
% 3.40/0.96  --problem_path                          ""
% 3.40/0.96  --include_path                          ""
% 3.40/0.96  --clausifier                            res/vclausify_rel
% 3.40/0.96  --clausifier_options                    --mode clausify
% 3.40/0.96  --stdin                                 false
% 3.40/0.96  --stats_out                             all
% 3.40/0.96  
% 3.40/0.96  ------ General Options
% 3.40/0.96  
% 3.40/0.96  --fof                                   false
% 3.40/0.96  --time_out_real                         305.
% 3.40/0.96  --time_out_virtual                      -1.
% 3.40/0.96  --symbol_type_check                     false
% 3.40/0.96  --clausify_out                          false
% 3.40/0.96  --sig_cnt_out                           false
% 3.40/0.96  --trig_cnt_out                          false
% 3.40/0.96  --trig_cnt_out_tolerance                1.
% 3.40/0.96  --trig_cnt_out_sk_spl                   false
% 3.40/0.96  --abstr_cl_out                          false
% 3.40/0.96  
% 3.40/0.96  ------ Global Options
% 3.40/0.96  
% 3.40/0.96  --schedule                              default
% 3.40/0.96  --add_important_lit                     false
% 3.40/0.96  --prop_solver_per_cl                    1000
% 3.40/0.96  --min_unsat_core                        false
% 3.40/0.96  --soft_assumptions                      false
% 3.40/0.96  --soft_lemma_size                       3
% 3.40/0.96  --prop_impl_unit_size                   0
% 3.40/0.96  --prop_impl_unit                        []
% 3.40/0.96  --share_sel_clauses                     true
% 3.40/0.96  --reset_solvers                         false
% 3.40/0.96  --bc_imp_inh                            [conj_cone]
% 3.40/0.96  --conj_cone_tolerance                   3.
% 3.40/0.96  --extra_neg_conj                        none
% 3.40/0.96  --large_theory_mode                     true
% 3.40/0.96  --prolific_symb_bound                   200
% 3.40/0.96  --lt_threshold                          2000
% 3.40/0.96  --clause_weak_htbl                      true
% 3.40/0.96  --gc_record_bc_elim                     false
% 3.40/0.96  
% 3.40/0.96  ------ Preprocessing Options
% 3.40/0.96  
% 3.40/0.96  --preprocessing_flag                    true
% 3.40/0.96  --time_out_prep_mult                    0.1
% 3.40/0.96  --splitting_mode                        input
% 3.40/0.96  --splitting_grd                         true
% 3.40/0.96  --splitting_cvd                         false
% 3.40/0.96  --splitting_cvd_svl                     false
% 3.40/0.96  --splitting_nvd                         32
% 3.40/0.96  --sub_typing                            true
% 3.40/0.96  --prep_gs_sim                           true
% 3.40/0.96  --prep_unflatten                        true
% 3.40/0.96  --prep_res_sim                          true
% 3.40/0.96  --prep_upred                            true
% 3.40/0.96  --prep_sem_filter                       exhaustive
% 3.40/0.96  --prep_sem_filter_out                   false
% 3.40/0.96  --pred_elim                             true
% 3.40/0.96  --res_sim_input                         true
% 3.40/0.96  --eq_ax_congr_red                       true
% 3.40/0.96  --pure_diseq_elim                       true
% 3.40/0.96  --brand_transform                       false
% 3.40/0.96  --non_eq_to_eq                          false
% 3.40/0.96  --prep_def_merge                        true
% 3.40/0.96  --prep_def_merge_prop_impl              false
% 3.40/0.96  --prep_def_merge_mbd                    true
% 3.40/0.96  --prep_def_merge_tr_red                 false
% 3.40/0.96  --prep_def_merge_tr_cl                  false
% 3.40/0.96  --smt_preprocessing                     true
% 3.40/0.96  --smt_ac_axioms                         fast
% 3.40/0.96  --preprocessed_out                      false
% 3.40/0.96  --preprocessed_stats                    false
% 3.40/0.96  
% 3.40/0.96  ------ Abstraction refinement Options
% 3.40/0.96  
% 3.40/0.96  --abstr_ref                             []
% 3.40/0.96  --abstr_ref_prep                        false
% 3.40/0.96  --abstr_ref_until_sat                   false
% 3.40/0.96  --abstr_ref_sig_restrict                funpre
% 3.40/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 3.40/0.96  --abstr_ref_under                       []
% 3.40/0.96  
% 3.40/0.96  ------ SAT Options
% 3.40/0.96  
% 3.40/0.96  --sat_mode                              false
% 3.40/0.96  --sat_fm_restart_options                ""
% 3.40/0.96  --sat_gr_def                            false
% 3.40/0.96  --sat_epr_types                         true
% 3.40/0.96  --sat_non_cyclic_types                  false
% 3.40/0.96  --sat_finite_models                     false
% 3.40/0.96  --sat_fm_lemmas                         false
% 3.40/0.96  --sat_fm_prep                           false
% 3.40/0.96  --sat_fm_uc_incr                        true
% 3.40/0.96  --sat_out_model                         small
% 3.40/0.96  --sat_out_clauses                       false
% 3.40/0.96  
% 3.40/0.96  ------ QBF Options
% 3.40/0.96  
% 3.40/0.96  --qbf_mode                              false
% 3.40/0.96  --qbf_elim_univ                         false
% 3.40/0.96  --qbf_dom_inst                          none
% 3.40/0.96  --qbf_dom_pre_inst                      false
% 3.40/0.96  --qbf_sk_in                             false
% 3.40/0.96  --qbf_pred_elim                         true
% 3.40/0.96  --qbf_split                             512
% 3.40/0.96  
% 3.40/0.96  ------ BMC1 Options
% 3.40/0.96  
% 3.40/0.96  --bmc1_incremental                      false
% 3.40/0.96  --bmc1_axioms                           reachable_all
% 3.40/0.96  --bmc1_min_bound                        0
% 3.40/0.96  --bmc1_max_bound                        -1
% 3.40/0.96  --bmc1_max_bound_default                -1
% 3.40/0.96  --bmc1_symbol_reachability              true
% 3.40/0.96  --bmc1_property_lemmas                  false
% 3.40/0.96  --bmc1_k_induction                      false
% 3.40/0.96  --bmc1_non_equiv_states                 false
% 3.40/0.96  --bmc1_deadlock                         false
% 3.40/0.96  --bmc1_ucm                              false
% 3.40/0.96  --bmc1_add_unsat_core                   none
% 3.40/0.96  --bmc1_unsat_core_children              false
% 3.40/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 3.40/0.96  --bmc1_out_stat                         full
% 3.40/0.96  --bmc1_ground_init                      false
% 3.40/0.96  --bmc1_pre_inst_next_state              false
% 3.40/0.96  --bmc1_pre_inst_state                   false
% 3.40/0.96  --bmc1_pre_inst_reach_state             false
% 3.40/0.96  --bmc1_out_unsat_core                   false
% 3.40/0.96  --bmc1_aig_witness_out                  false
% 3.40/0.96  --bmc1_verbose                          false
% 3.40/0.96  --bmc1_dump_clauses_tptp                false
% 3.40/0.96  --bmc1_dump_unsat_core_tptp             false
% 3.40/0.96  --bmc1_dump_file                        -
% 3.40/0.96  --bmc1_ucm_expand_uc_limit              128
% 3.40/0.96  --bmc1_ucm_n_expand_iterations          6
% 3.40/0.96  --bmc1_ucm_extend_mode                  1
% 3.40/0.96  --bmc1_ucm_init_mode                    2
% 3.40/0.96  --bmc1_ucm_cone_mode                    none
% 3.40/0.96  --bmc1_ucm_reduced_relation_type        0
% 3.40/0.96  --bmc1_ucm_relax_model                  4
% 3.40/0.96  --bmc1_ucm_full_tr_after_sat            true
% 3.40/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 3.40/0.96  --bmc1_ucm_layered_model                none
% 3.40/0.96  --bmc1_ucm_max_lemma_size               10
% 3.40/0.96  
% 3.40/0.96  ------ AIG Options
% 3.40/0.96  
% 3.40/0.96  --aig_mode                              false
% 3.40/0.96  
% 3.40/0.96  ------ Instantiation Options
% 3.40/0.96  
% 3.40/0.96  --instantiation_flag                    true
% 3.40/0.96  --inst_sos_flag                         false
% 3.40/0.96  --inst_sos_phase                        true
% 3.40/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.40/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.40/0.96  --inst_lit_sel_side                     none
% 3.40/0.96  --inst_solver_per_active                1400
% 3.40/0.96  --inst_solver_calls_frac                1.
% 3.40/0.96  --inst_passive_queue_type               priority_queues
% 3.40/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.40/0.96  --inst_passive_queues_freq              [25;2]
% 3.40/0.96  --inst_dismatching                      true
% 3.40/0.96  --inst_eager_unprocessed_to_passive     true
% 3.40/0.96  --inst_prop_sim_given                   true
% 3.40/0.96  --inst_prop_sim_new                     false
% 3.40/0.96  --inst_subs_new                         false
% 3.40/0.96  --inst_eq_res_simp                      false
% 3.40/0.96  --inst_subs_given                       false
% 3.40/0.96  --inst_orphan_elimination               true
% 3.40/0.96  --inst_learning_loop_flag               true
% 3.40/0.96  --inst_learning_start                   3000
% 3.40/0.96  --inst_learning_factor                  2
% 3.40/0.96  --inst_start_prop_sim_after_learn       3
% 3.40/0.96  --inst_sel_renew                        solver
% 3.40/0.96  --inst_lit_activity_flag                true
% 3.40/0.96  --inst_restr_to_given                   false
% 3.40/0.96  --inst_activity_threshold               500
% 3.40/0.96  --inst_out_proof                        true
% 3.40/0.96  
% 3.40/0.96  ------ Resolution Options
% 3.40/0.96  
% 3.40/0.96  --resolution_flag                       false
% 3.40/0.96  --res_lit_sel                           adaptive
% 3.40/0.96  --res_lit_sel_side                      none
% 3.40/0.96  --res_ordering                          kbo
% 3.40/0.96  --res_to_prop_solver                    active
% 3.40/0.96  --res_prop_simpl_new                    false
% 3.40/0.96  --res_prop_simpl_given                  true
% 3.40/0.96  --res_passive_queue_type                priority_queues
% 3.40/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.40/0.96  --res_passive_queues_freq               [15;5]
% 3.40/0.96  --res_forward_subs                      full
% 3.40/0.96  --res_backward_subs                     full
% 3.40/0.96  --res_forward_subs_resolution           true
% 3.40/0.96  --res_backward_subs_resolution          true
% 3.40/0.96  --res_orphan_elimination                true
% 3.40/0.96  --res_time_limit                        2.
% 3.40/0.96  --res_out_proof                         true
% 3.40/0.96  
% 3.40/0.96  ------ Superposition Options
% 3.40/0.96  
% 3.40/0.96  --superposition_flag                    true
% 3.40/0.96  --sup_passive_queue_type                priority_queues
% 3.40/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.40/0.96  --sup_passive_queues_freq               [8;1;4]
% 3.40/0.96  --demod_completeness_check              fast
% 3.40/0.96  --demod_use_ground                      true
% 3.40/0.96  --sup_to_prop_solver                    passive
% 3.40/0.96  --sup_prop_simpl_new                    true
% 3.40/0.96  --sup_prop_simpl_given                  true
% 3.40/0.96  --sup_fun_splitting                     false
% 3.40/0.96  --sup_smt_interval                      50000
% 3.40/0.96  
% 3.40/0.96  ------ Superposition Simplification Setup
% 3.40/0.96  
% 3.40/0.96  --sup_indices_passive                   []
% 3.40/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.40/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.40/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.40/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 3.40/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.40/0.96  --sup_full_bw                           [BwDemod]
% 3.40/0.96  --sup_immed_triv                        [TrivRules]
% 3.40/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.40/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.40/0.96  --sup_immed_bw_main                     []
% 3.40/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.40/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 3.40/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.40/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.40/0.96  
% 3.40/0.96  ------ Combination Options
% 3.40/0.96  
% 3.40/0.96  --comb_res_mult                         3
% 3.40/0.96  --comb_sup_mult                         2
% 3.40/0.96  --comb_inst_mult                        10
% 3.40/0.96  
% 3.40/0.96  ------ Debug Options
% 3.40/0.96  
% 3.40/0.96  --dbg_backtrace                         false
% 3.40/0.96  --dbg_dump_prop_clauses                 false
% 3.40/0.96  --dbg_dump_prop_clauses_file            -
% 3.40/0.96  --dbg_out_stat                          false
% 3.40/0.96  
% 3.40/0.96  
% 3.40/0.96  
% 3.40/0.96  
% 3.40/0.96  ------ Proving...
% 3.40/0.96  
% 3.40/0.96  
% 3.40/0.96  % SZS status Theorem for theBenchmark.p
% 3.40/0.96  
% 3.40/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 3.40/0.96  
% 3.40/0.96  fof(f18,conjecture,(
% 3.40/0.96    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.40/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.96  
% 3.40/0.96  fof(f19,negated_conjecture,(
% 3.40/0.96    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.40/0.96    inference(negated_conjecture,[],[f18])).
% 3.40/0.96  
% 3.40/0.96  fof(f40,plain,(
% 3.40/0.96    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.40/0.96    inference(ennf_transformation,[],[f19])).
% 3.40/0.96  
% 3.40/0.96  fof(f41,plain,(
% 3.40/0.96    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.40/0.96    inference(flattening,[],[f40])).
% 3.40/0.96  
% 3.40/0.96  fof(f49,plain,(
% 3.40/0.96    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 3.40/0.96    introduced(choice_axiom,[])).
% 3.40/0.96  
% 3.40/0.96  fof(f50,plain,(
% 3.40/0.96    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 3.40/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f41,f49])).
% 3.40/0.96  
% 3.40/0.96  fof(f85,plain,(
% 3.40/0.96    r1_tarski(sK2,sK0)),
% 3.40/0.96    inference(cnf_transformation,[],[f50])).
% 3.40/0.96  
% 3.40/0.96  fof(f14,axiom,(
% 3.40/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.40/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.96  
% 3.40/0.96  fof(f32,plain,(
% 3.40/0.96    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.40/0.96    inference(ennf_transformation,[],[f14])).
% 3.40/0.96  
% 3.40/0.96  fof(f33,plain,(
% 3.40/0.96    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.40/0.96    inference(flattening,[],[f32])).
% 3.40/0.96  
% 3.40/0.96  fof(f48,plain,(
% 3.40/0.96    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.40/0.96    inference(nnf_transformation,[],[f33])).
% 3.40/0.96  
% 3.40/0.96  fof(f70,plain,(
% 3.40/0.96    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.40/0.96    inference(cnf_transformation,[],[f48])).
% 3.40/0.96  
% 3.40/0.96  fof(f83,plain,(
% 3.40/0.96    v1_funct_2(sK3,sK0,sK1)),
% 3.40/0.96    inference(cnf_transformation,[],[f50])).
% 3.40/0.96  
% 3.40/0.96  fof(f84,plain,(
% 3.40/0.96    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.40/0.96    inference(cnf_transformation,[],[f50])).
% 3.40/0.96  
% 3.40/0.96  fof(f13,axiom,(
% 3.40/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.40/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.96  
% 3.40/0.96  fof(f31,plain,(
% 3.40/0.96    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.40/0.96    inference(ennf_transformation,[],[f13])).
% 3.40/0.96  
% 3.40/0.96  fof(f69,plain,(
% 3.40/0.96    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.40/0.96    inference(cnf_transformation,[],[f31])).
% 3.40/0.96  
% 3.40/0.96  fof(f9,axiom,(
% 3.40/0.96    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 3.40/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.96  
% 3.40/0.96  fof(f26,plain,(
% 3.40/0.96    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 3.40/0.96    inference(ennf_transformation,[],[f9])).
% 3.40/0.96  
% 3.40/0.96  fof(f27,plain,(
% 3.40/0.96    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.40/0.96    inference(flattening,[],[f26])).
% 3.40/0.96  
% 3.40/0.96  fof(f65,plain,(
% 3.40/0.96    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.40/0.96    inference(cnf_transformation,[],[f27])).
% 3.40/0.96  
% 3.40/0.96  fof(f11,axiom,(
% 3.40/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.40/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.96  
% 3.40/0.96  fof(f29,plain,(
% 3.40/0.96    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.40/0.96    inference(ennf_transformation,[],[f11])).
% 3.40/0.96  
% 3.40/0.96  fof(f67,plain,(
% 3.40/0.96    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.40/0.96    inference(cnf_transformation,[],[f29])).
% 3.40/0.96  
% 3.40/0.96  fof(f17,axiom,(
% 3.40/0.96    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 3.40/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.96  
% 3.40/0.96  fof(f38,plain,(
% 3.40/0.96    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.40/0.96    inference(ennf_transformation,[],[f17])).
% 3.40/0.96  
% 3.40/0.96  fof(f39,plain,(
% 3.40/0.96    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.40/0.96    inference(flattening,[],[f38])).
% 3.40/0.96  
% 3.40/0.96  fof(f81,plain,(
% 3.40/0.96    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.40/0.96    inference(cnf_transformation,[],[f39])).
% 3.40/0.96  
% 3.40/0.96  fof(f16,axiom,(
% 3.40/0.96    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 3.40/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.96  
% 3.40/0.96  fof(f36,plain,(
% 3.40/0.96    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.40/0.96    inference(ennf_transformation,[],[f16])).
% 3.40/0.96  
% 3.40/0.96  fof(f37,plain,(
% 3.40/0.96    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.40/0.96    inference(flattening,[],[f36])).
% 3.40/0.96  
% 3.40/0.96  fof(f78,plain,(
% 3.40/0.96    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.40/0.96    inference(cnf_transformation,[],[f37])).
% 3.40/0.96  
% 3.40/0.96  fof(f82,plain,(
% 3.40/0.96    v1_funct_1(sK3)),
% 3.40/0.96    inference(cnf_transformation,[],[f50])).
% 3.40/0.96  
% 3.40/0.96  fof(f15,axiom,(
% 3.40/0.96    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 3.40/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.96  
% 3.40/0.96  fof(f34,plain,(
% 3.40/0.96    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.40/0.96    inference(ennf_transformation,[],[f15])).
% 3.40/0.96  
% 3.40/0.96  fof(f35,plain,(
% 3.40/0.96    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.40/0.96    inference(flattening,[],[f34])).
% 3.40/0.96  
% 3.40/0.96  fof(f76,plain,(
% 3.40/0.96    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.40/0.96    inference(cnf_transformation,[],[f35])).
% 3.40/0.96  
% 3.40/0.96  fof(f80,plain,(
% 3.40/0.96    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.40/0.96    inference(cnf_transformation,[],[f39])).
% 3.40/0.96  
% 3.40/0.96  fof(f87,plain,(
% 3.40/0.96    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 3.40/0.96    inference(cnf_transformation,[],[f50])).
% 3.40/0.96  
% 3.40/0.96  fof(f12,axiom,(
% 3.40/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.40/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.96  
% 3.40/0.96  fof(f20,plain,(
% 3.40/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.40/0.96    inference(pure_predicate_removal,[],[f12])).
% 3.40/0.96  
% 3.40/0.96  fof(f30,plain,(
% 3.40/0.96    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.40/0.96    inference(ennf_transformation,[],[f20])).
% 3.40/0.96  
% 3.40/0.96  fof(f68,plain,(
% 3.40/0.96    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.40/0.96    inference(cnf_transformation,[],[f30])).
% 3.40/0.96  
% 3.40/0.96  fof(f6,axiom,(
% 3.40/0.96    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.40/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.96  
% 3.40/0.96  fof(f23,plain,(
% 3.40/0.96    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.40/0.96    inference(ennf_transformation,[],[f6])).
% 3.40/0.96  
% 3.40/0.96  fof(f47,plain,(
% 3.40/0.96    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.40/0.96    inference(nnf_transformation,[],[f23])).
% 3.40/0.96  
% 3.40/0.96  fof(f61,plain,(
% 3.40/0.96    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.40/0.96    inference(cnf_transformation,[],[f47])).
% 3.40/0.96  
% 3.40/0.96  fof(f77,plain,(
% 3.40/0.96    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.40/0.96    inference(cnf_transformation,[],[f35])).
% 3.40/0.96  
% 3.40/0.96  fof(f86,plain,(
% 3.40/0.96    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 3.40/0.96    inference(cnf_transformation,[],[f50])).
% 3.40/0.96  
% 3.40/0.96  fof(f4,axiom,(
% 3.40/0.96    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.40/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.96  
% 3.40/0.96  fof(f44,plain,(
% 3.40/0.96    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.40/0.96    inference(nnf_transformation,[],[f4])).
% 3.40/0.96  
% 3.40/0.96  fof(f45,plain,(
% 3.40/0.96    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.40/0.96    inference(flattening,[],[f44])).
% 3.40/0.96  
% 3.40/0.96  fof(f57,plain,(
% 3.40/0.96    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.40/0.96    inference(cnf_transformation,[],[f45])).
% 3.40/0.96  
% 3.40/0.96  fof(f91,plain,(
% 3.40/0.96    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.40/0.96    inference(equality_resolution,[],[f57])).
% 3.40/0.96  
% 3.40/0.96  fof(f75,plain,(
% 3.40/0.96    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.40/0.96    inference(cnf_transformation,[],[f48])).
% 3.40/0.96  
% 3.40/0.96  fof(f92,plain,(
% 3.40/0.96    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.40/0.96    inference(equality_resolution,[],[f75])).
% 3.40/0.96  
% 3.40/0.96  fof(f93,plain,(
% 3.40/0.96    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.40/0.96    inference(equality_resolution,[],[f92])).
% 3.40/0.96  
% 3.40/0.96  fof(f58,plain,(
% 3.40/0.96    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.40/0.96    inference(cnf_transformation,[],[f45])).
% 3.40/0.96  
% 3.40/0.96  fof(f90,plain,(
% 3.40/0.96    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.40/0.96    inference(equality_resolution,[],[f58])).
% 3.40/0.96  
% 3.40/0.96  fof(f5,axiom,(
% 3.40/0.96    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.40/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.96  
% 3.40/0.96  fof(f46,plain,(
% 3.40/0.96    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.40/0.96    inference(nnf_transformation,[],[f5])).
% 3.40/0.96  
% 3.40/0.96  fof(f60,plain,(
% 3.40/0.96    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.40/0.96    inference(cnf_transformation,[],[f46])).
% 3.40/0.96  
% 3.40/0.96  fof(f3,axiom,(
% 3.40/0.96    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.40/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.96  
% 3.40/0.96  fof(f55,plain,(
% 3.40/0.96    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.40/0.96    inference(cnf_transformation,[],[f3])).
% 3.40/0.96  
% 3.40/0.96  fof(f56,plain,(
% 3.40/0.96    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.40/0.96    inference(cnf_transformation,[],[f45])).
% 3.40/0.96  
% 3.40/0.96  fof(f1,axiom,(
% 3.40/0.96    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.40/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.96  
% 3.40/0.96  fof(f42,plain,(
% 3.40/0.96    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.40/0.96    inference(nnf_transformation,[],[f1])).
% 3.40/0.96  
% 3.40/0.96  fof(f43,plain,(
% 3.40/0.96    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.40/0.96    inference(flattening,[],[f42])).
% 3.40/0.96  
% 3.40/0.96  fof(f53,plain,(
% 3.40/0.96    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.40/0.96    inference(cnf_transformation,[],[f43])).
% 3.40/0.96  
% 3.40/0.96  fof(f2,axiom,(
% 3.40/0.96    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.40/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.96  
% 3.40/0.96  fof(f21,plain,(
% 3.40/0.96    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.40/0.96    inference(ennf_transformation,[],[f2])).
% 3.40/0.96  
% 3.40/0.96  fof(f22,plain,(
% 3.40/0.96    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.40/0.96    inference(flattening,[],[f21])).
% 3.40/0.96  
% 3.40/0.96  fof(f54,plain,(
% 3.40/0.96    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.40/0.96    inference(cnf_transformation,[],[f22])).
% 3.40/0.96  
% 3.40/0.96  fof(f73,plain,(
% 3.40/0.96    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.40/0.96    inference(cnf_transformation,[],[f48])).
% 3.40/0.96  
% 3.40/0.96  fof(f95,plain,(
% 3.40/0.96    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.40/0.96    inference(equality_resolution,[],[f73])).
% 3.40/0.96  
% 3.40/0.96  fof(f8,axiom,(
% 3.40/0.96    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0))),
% 3.40/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.96  
% 3.40/0.96  fof(f25,plain,(
% 3.40/0.96    ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 3.40/0.96    inference(ennf_transformation,[],[f8])).
% 3.40/0.96  
% 3.40/0.96  fof(f64,plain,(
% 3.40/0.96    ( ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 3.40/0.96    inference(cnf_transformation,[],[f25])).
% 3.40/0.96  
% 3.40/0.96  fof(f7,axiom,(
% 3.40/0.96    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 3.40/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.96  
% 3.40/0.96  fof(f24,plain,(
% 3.40/0.96    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 3.40/0.96    inference(ennf_transformation,[],[f7])).
% 3.40/0.96  
% 3.40/0.96  fof(f63,plain,(
% 3.40/0.96    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 3.40/0.96    inference(cnf_transformation,[],[f24])).
% 3.40/0.96  
% 3.40/0.96  fof(f71,plain,(
% 3.40/0.96    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.40/0.96    inference(cnf_transformation,[],[f48])).
% 3.40/0.96  
% 3.40/0.96  fof(f96,plain,(
% 3.40/0.96    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.40/0.96    inference(equality_resolution,[],[f71])).
% 3.40/0.96  
% 3.40/0.96  cnf(c_33,negated_conjecture,
% 3.40/0.96      ( r1_tarski(sK2,sK0) ),
% 3.40/0.96      inference(cnf_transformation,[],[f85]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_1717,plain,
% 3.40/0.96      ( r1_tarski(sK2,sK0) = iProver_top ),
% 3.40/0.96      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_24,plain,
% 3.40/0.96      ( ~ v1_funct_2(X0,X1,X2)
% 3.40/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.40/0.96      | k1_relset_1(X1,X2,X0) = X1
% 3.40/0.96      | k1_xboole_0 = X2 ),
% 3.40/0.96      inference(cnf_transformation,[],[f70]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_35,negated_conjecture,
% 3.40/0.96      ( v1_funct_2(sK3,sK0,sK1) ),
% 3.40/0.96      inference(cnf_transformation,[],[f83]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_631,plain,
% 3.40/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.40/0.96      | k1_relset_1(X1,X2,X0) = X1
% 3.40/0.96      | sK3 != X0
% 3.40/0.96      | sK1 != X2
% 3.40/0.96      | sK0 != X1
% 3.40/0.96      | k1_xboole_0 = X2 ),
% 3.40/0.96      inference(resolution_lifted,[status(thm)],[c_24,c_35]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_632,plain,
% 3.40/0.96      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.40/0.96      | k1_relset_1(sK0,sK1,sK3) = sK0
% 3.40/0.96      | k1_xboole_0 = sK1 ),
% 3.40/0.96      inference(unflattening,[status(thm)],[c_631]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_34,negated_conjecture,
% 3.40/0.96      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.40/0.96      inference(cnf_transformation,[],[f84]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_634,plain,
% 3.40/0.96      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 3.40/0.96      inference(global_propositional_subsumption,
% 3.40/0.96                [status(thm)],
% 3.40/0.96                [c_632,c_34]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_1716,plain,
% 3.40/0.96      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.40/0.96      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_18,plain,
% 3.40/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.40/0.96      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.40/0.96      inference(cnf_transformation,[],[f69]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_1722,plain,
% 3.40/0.96      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.40/0.96      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.40/0.96      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_3736,plain,
% 3.40/0.96      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 3.40/0.96      inference(superposition,[status(thm)],[c_1716,c_1722]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_3883,plain,
% 3.40/0.96      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 3.40/0.96      inference(superposition,[status(thm)],[c_634,c_3736]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_14,plain,
% 3.40/0.96      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.40/0.96      | ~ v1_relat_1(X1)
% 3.40/0.96      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 3.40/0.96      inference(cnf_transformation,[],[f65]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_1725,plain,
% 3.40/0.96      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 3.40/0.96      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 3.40/0.96      | v1_relat_1(X0) != iProver_top ),
% 3.40/0.96      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_5007,plain,
% 3.40/0.96      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 3.40/0.96      | sK1 = k1_xboole_0
% 3.40/0.96      | r1_tarski(X0,sK0) != iProver_top
% 3.40/0.96      | v1_relat_1(sK3) != iProver_top ),
% 3.40/0.96      inference(superposition,[status(thm)],[c_3883,c_1725]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_39,plain,
% 3.40/0.96      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.40/0.96      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_16,plain,
% 3.40/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.40/0.96      | v1_relat_1(X0) ),
% 3.40/0.96      inference(cnf_transformation,[],[f67]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_2008,plain,
% 3.40/0.96      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.40/0.96      | v1_relat_1(sK3) ),
% 3.40/0.96      inference(instantiation,[status(thm)],[c_16]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_2009,plain,
% 3.40/0.96      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.40/0.96      | v1_relat_1(sK3) = iProver_top ),
% 3.40/0.96      inference(predicate_to_equality,[status(thm)],[c_2008]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_5514,plain,
% 3.40/0.96      ( r1_tarski(X0,sK0) != iProver_top
% 3.40/0.96      | sK1 = k1_xboole_0
% 3.40/0.96      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 3.40/0.96      inference(global_propositional_subsumption,
% 3.40/0.96                [status(thm)],
% 3.40/0.96                [c_5007,c_39,c_2009]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_5515,plain,
% 3.40/0.96      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 3.40/0.96      | sK1 = k1_xboole_0
% 3.40/0.96      | r1_tarski(X0,sK0) != iProver_top ),
% 3.40/0.96      inference(renaming,[status(thm)],[c_5514]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_5525,plain,
% 3.40/0.96      ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 | sK1 = k1_xboole_0 ),
% 3.40/0.96      inference(superposition,[status(thm)],[c_1717,c_5515]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_28,plain,
% 3.40/0.96      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.40/0.96      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.40/0.96      | ~ v1_funct_1(X0)
% 3.40/0.96      | ~ v1_relat_1(X0) ),
% 3.40/0.96      inference(cnf_transformation,[],[f81]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_1718,plain,
% 3.40/0.96      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 3.40/0.96      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.40/0.96      | v1_funct_1(X0) != iProver_top
% 3.40/0.96      | v1_relat_1(X0) != iProver_top ),
% 3.40/0.96      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_6194,plain,
% 3.40/0.96      ( sK1 = k1_xboole_0
% 3.40/0.96      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 3.40/0.96      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
% 3.40/0.96      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
% 3.40/0.96      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.40/0.96      inference(superposition,[status(thm)],[c_5525,c_1718]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_27,plain,
% 3.40/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.40/0.96      | ~ v1_funct_1(X0)
% 3.40/0.96      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 3.40/0.96      inference(cnf_transformation,[],[f78]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_1719,plain,
% 3.40/0.96      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 3.40/0.96      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.40/0.96      | v1_funct_1(X2) != iProver_top ),
% 3.40/0.96      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_5927,plain,
% 3.40/0.96      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
% 3.40/0.96      | v1_funct_1(sK3) != iProver_top ),
% 3.40/0.96      inference(superposition,[status(thm)],[c_1716,c_1719]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_36,negated_conjecture,
% 3.40/0.96      ( v1_funct_1(sK3) ),
% 3.40/0.96      inference(cnf_transformation,[],[f82]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_2082,plain,
% 3.40/0.96      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.40/0.96      | ~ v1_funct_1(sK3)
% 3.40/0.96      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 3.40/0.96      inference(instantiation,[status(thm)],[c_27]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_2196,plain,
% 3.40/0.96      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.40/0.96      | ~ v1_funct_1(sK3)
% 3.40/0.96      | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 3.40/0.96      inference(instantiation,[status(thm)],[c_2082]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_6134,plain,
% 3.40/0.96      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 3.40/0.96      inference(global_propositional_subsumption,
% 3.40/0.96                [status(thm)],
% 3.40/0.96                [c_5927,c_36,c_34,c_2196]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_26,plain,
% 3.40/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.40/0.96      | ~ v1_funct_1(X0)
% 3.40/0.96      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 3.40/0.96      inference(cnf_transformation,[],[f76]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_1720,plain,
% 3.40/0.96      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.40/0.96      | v1_funct_1(X0) != iProver_top
% 3.40/0.96      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
% 3.40/0.96      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_5693,plain,
% 3.40/0.96      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 3.40/0.96      | v1_funct_1(sK3) != iProver_top ),
% 3.40/0.96      inference(superposition,[status(thm)],[c_1716,c_1720]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_37,plain,
% 3.40/0.96      ( v1_funct_1(sK3) = iProver_top ),
% 3.40/0.96      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_2058,plain,
% 3.40/0.96      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.40/0.96      | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
% 3.40/0.96      | ~ v1_funct_1(sK3) ),
% 3.40/0.96      inference(instantiation,[status(thm)],[c_26]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_2164,plain,
% 3.40/0.96      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.40/0.96      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
% 3.40/0.96      | ~ v1_funct_1(sK3) ),
% 3.40/0.96      inference(instantiation,[status(thm)],[c_2058]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_2165,plain,
% 3.40/0.96      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.40/0.96      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 3.40/0.96      | v1_funct_1(sK3) != iProver_top ),
% 3.40/0.96      inference(predicate_to_equality,[status(thm)],[c_2164]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_5974,plain,
% 3.40/0.96      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
% 3.40/0.96      inference(global_propositional_subsumption,
% 3.40/0.96                [status(thm)],
% 3.40/0.96                [c_5693,c_37,c_39,c_2165]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_6143,plain,
% 3.40/0.96      ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 3.40/0.96      inference(demodulation,[status(thm)],[c_6134,c_5974]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_8236,plain,
% 3.40/0.96      ( sK1 = k1_xboole_0
% 3.40/0.96      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 3.40/0.96      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
% 3.40/0.96      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.40/0.96      inference(forward_subsumption_resolution,
% 3.40/0.96                [status(thm)],
% 3.40/0.96                [c_6194,c_6143]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_29,plain,
% 3.40/0.96      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.40/0.96      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.40/0.96      | ~ v1_funct_1(X0)
% 3.40/0.96      | ~ v1_relat_1(X0) ),
% 3.40/0.96      inference(cnf_transformation,[],[f80]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_31,negated_conjecture,
% 3.40/0.96      ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
% 3.40/0.96      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.40/0.96      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 3.40/0.96      inference(cnf_transformation,[],[f87]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_642,plain,
% 3.40/0.96      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.40/0.96      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.40/0.96      | ~ v1_funct_1(X0)
% 3.40/0.96      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.40/0.96      | ~ v1_relat_1(X0)
% 3.40/0.96      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 3.40/0.96      | k1_relat_1(X0) != sK2
% 3.40/0.96      | sK1 != X1 ),
% 3.40/0.96      inference(resolution_lifted,[status(thm)],[c_29,c_31]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_643,plain,
% 3.40/0.96      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.40/0.96      | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
% 3.40/0.96      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.40/0.96      | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.40/0.96      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
% 3.40/0.96      inference(unflattening,[status(thm)],[c_642]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_17,plain,
% 3.40/0.96      ( v5_relat_1(X0,X1)
% 3.40/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.40/0.96      inference(cnf_transformation,[],[f68]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_11,plain,
% 3.40/0.96      ( ~ v5_relat_1(X0,X1)
% 3.40/0.96      | r1_tarski(k2_relat_1(X0),X1)
% 3.40/0.96      | ~ v1_relat_1(X0) ),
% 3.40/0.96      inference(cnf_transformation,[],[f61]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_430,plain,
% 3.40/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.40/0.96      | r1_tarski(k2_relat_1(X0),X2)
% 3.40/0.96      | ~ v1_relat_1(X0) ),
% 3.40/0.96      inference(resolution,[status(thm)],[c_17,c_11]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_434,plain,
% 3.40/0.96      ( r1_tarski(k2_relat_1(X0),X2)
% 3.40/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.40/0.96      inference(global_propositional_subsumption,
% 3.40/0.96                [status(thm)],
% 3.40/0.96                [c_430,c_16]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_435,plain,
% 3.40/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.40/0.96      | r1_tarski(k2_relat_1(X0),X2) ),
% 3.40/0.96      inference(renaming,[status(thm)],[c_434]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_655,plain,
% 3.40/0.96      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.40/0.96      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.40/0.96      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
% 3.40/0.96      inference(forward_subsumption_resolution,
% 3.40/0.96                [status(thm)],
% 3.40/0.96                [c_643,c_16,c_435]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_1705,plain,
% 3.40/0.96      ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 3.40/0.96      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.40/0.96      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.40/0.96      inference(predicate_to_equality,[status(thm)],[c_655]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_6141,plain,
% 3.40/0.96      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 3.40/0.96      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.40/0.96      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.40/0.96      inference(demodulation,[status(thm)],[c_6134,c_1705]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_6157,plain,
% 3.40/0.96      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 3.40/0.96      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.40/0.96      inference(forward_subsumption_resolution,
% 3.40/0.96                [status(thm)],
% 3.40/0.96                [c_6141,c_6143]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_10154,plain,
% 3.40/0.96      ( sK1 = k1_xboole_0
% 3.40/0.96      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.40/0.96      inference(superposition,[status(thm)],[c_5525,c_6157]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_10231,plain,
% 3.40/0.96      ( sK1 = k1_xboole_0
% 3.40/0.96      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
% 3.40/0.96      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.40/0.96      inference(superposition,[status(thm)],[c_8236,c_10154]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_25,plain,
% 3.40/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.40/0.96      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.40/0.96      | ~ v1_funct_1(X0) ),
% 3.40/0.96      inference(cnf_transformation,[],[f77]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_1721,plain,
% 3.40/0.96      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.40/0.96      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.40/0.96      | v1_funct_1(X0) != iProver_top ),
% 3.40/0.96      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_7087,plain,
% 3.40/0.96      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 3.40/0.96      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.40/0.96      | v1_funct_1(sK3) != iProver_top ),
% 3.40/0.96      inference(superposition,[status(thm)],[c_6134,c_1721]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_7909,plain,
% 3.40/0.96      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.40/0.96      inference(global_propositional_subsumption,
% 3.40/0.96                [status(thm)],
% 3.40/0.96                [c_7087,c_37,c_39]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_1723,plain,
% 3.40/0.96      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.40/0.96      | v1_relat_1(X0) = iProver_top ),
% 3.40/0.96      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_7922,plain,
% 3.40/0.96      ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 3.40/0.96      inference(superposition,[status(thm)],[c_7909,c_1723]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_1714,plain,
% 3.40/0.96      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.40/0.96      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 3.40/0.96      inference(predicate_to_equality,[status(thm)],[c_435]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_7921,plain,
% 3.40/0.96      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top ),
% 3.40/0.96      inference(superposition,[status(thm)],[c_7909,c_1714]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_14344,plain,
% 3.40/0.96      ( sK1 = k1_xboole_0 ),
% 3.40/0.96      inference(forward_subsumption_resolution,
% 3.40/0.96                [status(thm)],
% 3.40/0.96                [c_10231,c_7922,c_7921]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_14372,plain,
% 3.40/0.96      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
% 3.40/0.96      inference(demodulation,[status(thm)],[c_14344,c_7909]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_32,negated_conjecture,
% 3.40/0.96      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 3.40/0.96      inference(cnf_transformation,[],[f86]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_14389,plain,
% 3.40/0.96      ( sK0 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.40/0.96      inference(demodulation,[status(thm)],[c_14344,c_32]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_14390,plain,
% 3.40/0.96      ( sK0 = k1_xboole_0 ),
% 3.40/0.96      inference(equality_resolution_simp,[status(thm)],[c_14389]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_14447,plain,
% 3.40/0.96      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.40/0.96      inference(light_normalisation,[status(thm)],[c_14372,c_14390]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_6,plain,
% 3.40/0.96      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.40/0.96      inference(cnf_transformation,[],[f91]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_14449,plain,
% 3.40/0.96      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.40/0.96      inference(demodulation,[status(thm)],[c_14447,c_6]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_19,plain,
% 3.40/0.96      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 3.40/0.96      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 3.40/0.96      | k1_xboole_0 = X0 ),
% 3.40/0.96      inference(cnf_transformation,[],[f93]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_459,plain,
% 3.40/0.96      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.40/0.96      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 3.40/0.96      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.40/0.96      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.40/0.96      | sK2 != X0
% 3.40/0.96      | sK1 != k1_xboole_0
% 3.40/0.96      | k1_xboole_0 = X0 ),
% 3.40/0.96      inference(resolution_lifted,[status(thm)],[c_19,c_31]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_460,plain,
% 3.40/0.96      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.40/0.96      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
% 3.40/0.96      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.40/0.96      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.40/0.96      | sK1 != k1_xboole_0
% 3.40/0.96      | k1_xboole_0 = sK2 ),
% 3.40/0.96      inference(unflattening,[status(thm)],[c_459]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_1713,plain,
% 3.40/0.96      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.40/0.96      | sK1 != k1_xboole_0
% 3.40/0.96      | k1_xboole_0 = sK2
% 3.40/0.96      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.40/0.96      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
% 3.40/0.96      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.40/0.96      inference(predicate_to_equality,[status(thm)],[c_460]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_5,plain,
% 3.40/0.96      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.40/0.96      inference(cnf_transformation,[],[f90]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_1905,plain,
% 3.40/0.96      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.40/0.96      | sK2 = k1_xboole_0
% 3.40/0.96      | sK1 != k1_xboole_0
% 3.40/0.96      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.40/0.96      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.40/0.96      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.40/0.96      inference(demodulation,[status(thm)],[c_1713,c_5]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_8,plain,
% 3.40/0.96      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.40/0.96      inference(cnf_transformation,[],[f60]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_106,plain,
% 3.40/0.96      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.40/0.96      | r1_tarski(X0,X1) != iProver_top ),
% 3.40/0.96      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_108,plain,
% 3.40/0.96      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.40/0.96      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.40/0.96      inference(instantiation,[status(thm)],[c_106]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_4,plain,
% 3.40/0.96      ( r1_tarski(k1_xboole_0,X0) ),
% 3.40/0.96      inference(cnf_transformation,[],[f55]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_111,plain,
% 3.40/0.96      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.40/0.96      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_113,plain,
% 3.40/0.96      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.40/0.96      inference(instantiation,[status(thm)],[c_111]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_2282,plain,
% 3.40/0.96      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.40/0.96      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.40/0.96      | ~ v1_funct_1(sK3) ),
% 3.40/0.96      inference(instantiation,[status(thm)],[c_2164]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_2283,plain,
% 3.40/0.96      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.40/0.96      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) = iProver_top
% 3.40/0.96      | v1_funct_1(sK3) != iProver_top ),
% 3.40/0.96      inference(predicate_to_equality,[status(thm)],[c_2282]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_2346,plain,
% 3.40/0.96      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.40/0.96      | sK2 = k1_xboole_0
% 3.40/0.96      | sK1 != k1_xboole_0
% 3.40/0.96      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.40/0.96      inference(global_propositional_subsumption,
% 3.40/0.96                [status(thm)],
% 3.40/0.96                [c_1905,c_37,c_39,c_108,c_113,c_2283]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_6139,plain,
% 3.40/0.96      ( k7_relat_1(sK3,sK2) != k1_xboole_0
% 3.40/0.96      | sK2 = k1_xboole_0
% 3.40/0.96      | sK1 != k1_xboole_0
% 3.40/0.96      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.40/0.96      inference(demodulation,[status(thm)],[c_6134,c_2346]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_7,plain,
% 3.40/0.96      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.40/0.96      | k1_xboole_0 = X1
% 3.40/0.96      | k1_xboole_0 = X0 ),
% 3.40/0.96      inference(cnf_transformation,[],[f56]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_109,plain,
% 3.40/0.96      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.40/0.96      | k1_xboole_0 = k1_xboole_0 ),
% 3.40/0.96      inference(instantiation,[status(thm)],[c_7]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_110,plain,
% 3.40/0.96      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.40/0.96      inference(instantiation,[status(thm)],[c_6]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_112,plain,
% 3.40/0.96      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.40/0.96      inference(instantiation,[status(thm)],[c_4]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_0,plain,
% 3.40/0.96      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.40/0.96      inference(cnf_transformation,[],[f53]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_2030,plain,
% 3.40/0.96      ( ~ r1_tarski(sK2,k1_xboole_0)
% 3.40/0.96      | ~ r1_tarski(k1_xboole_0,sK2)
% 3.40/0.96      | sK2 = k1_xboole_0 ),
% 3.40/0.96      inference(instantiation,[status(thm)],[c_0]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_1009,plain,
% 3.40/0.96      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.40/0.96      theory(equality) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_2303,plain,
% 3.40/0.96      ( ~ r1_tarski(X0,X1)
% 3.40/0.96      | r1_tarski(sK0,k1_xboole_0)
% 3.40/0.96      | sK0 != X0
% 3.40/0.96      | k1_xboole_0 != X1 ),
% 3.40/0.96      inference(instantiation,[status(thm)],[c_1009]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_2305,plain,
% 3.40/0.96      ( r1_tarski(sK0,k1_xboole_0)
% 3.40/0.96      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 3.40/0.96      | sK0 != k1_xboole_0
% 3.40/0.96      | k1_xboole_0 != k1_xboole_0 ),
% 3.40/0.96      inference(instantiation,[status(thm)],[c_2303]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_1008,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_2046,plain,
% 3.40/0.96      ( sK0 != X0 | sK0 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.40/0.96      inference(instantiation,[status(thm)],[c_1008]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_2385,plain,
% 3.40/0.96      ( sK0 != sK0 | sK0 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 3.40/0.96      inference(instantiation,[status(thm)],[c_2046]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_1007,plain,( X0 = X0 ),theory(equality) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_2386,plain,
% 3.40/0.96      ( sK0 = sK0 ),
% 3.40/0.96      inference(instantiation,[status(thm)],[c_1007]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_3042,plain,
% 3.40/0.96      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 3.40/0.96      inference(instantiation,[status(thm)],[c_1008]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_3043,plain,
% 3.40/0.96      ( sK1 != k1_xboole_0
% 3.40/0.96      | k1_xboole_0 = sK1
% 3.40/0.96      | k1_xboole_0 != k1_xboole_0 ),
% 3.40/0.96      inference(instantiation,[status(thm)],[c_3042]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_3,plain,
% 3.40/0.96      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 3.40/0.96      inference(cnf_transformation,[],[f54]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_2289,plain,
% 3.40/0.96      ( ~ r1_tarski(X0,k1_xboole_0)
% 3.40/0.96      | ~ r1_tarski(sK2,X0)
% 3.40/0.96      | r1_tarski(sK2,k1_xboole_0) ),
% 3.40/0.96      inference(instantiation,[status(thm)],[c_3]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_3188,plain,
% 3.40/0.96      ( ~ r1_tarski(sK2,sK0)
% 3.40/0.96      | r1_tarski(sK2,k1_xboole_0)
% 3.40/0.96      | ~ r1_tarski(sK0,k1_xboole_0) ),
% 3.40/0.96      inference(instantiation,[status(thm)],[c_2289]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_3958,plain,
% 3.40/0.96      ( r1_tarski(k1_xboole_0,sK2) ),
% 3.40/0.96      inference(instantiation,[status(thm)],[c_4]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_6409,plain,
% 3.40/0.96      ( sK2 = k1_xboole_0
% 3.40/0.96      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.40/0.96      inference(global_propositional_subsumption,
% 3.40/0.96                [status(thm)],
% 3.40/0.96                [c_6139,c_33,c_32,c_109,c_110,c_112,c_2030,c_2305,c_2385,
% 3.40/0.96                 c_2386,c_3043,c_3188,c_3958,c_5525,c_6157]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_14375,plain,
% 3.40/0.96      ( sK2 = k1_xboole_0
% 3.40/0.96      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 3.40/0.96      inference(demodulation,[status(thm)],[c_14344,c_6409]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_14438,plain,
% 3.40/0.96      ( sK2 = k1_xboole_0
% 3.40/0.96      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.40/0.96      inference(demodulation,[status(thm)],[c_14375,c_5]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_14451,plain,
% 3.40/0.96      ( sK2 = k1_xboole_0 ),
% 3.40/0.96      inference(backward_subsumption_resolution,
% 3.40/0.96                [status(thm)],
% 3.40/0.96                [c_14449,c_14438]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_21,plain,
% 3.40/0.96      ( v1_funct_2(X0,k1_xboole_0,X1)
% 3.40/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.40/0.96      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 3.40/0.96      inference(cnf_transformation,[],[f95]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_556,plain,
% 3.40/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.40/0.96      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.40/0.96      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.40/0.96      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 3.40/0.96      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 3.40/0.96      | sK2 != k1_xboole_0
% 3.40/0.96      | sK1 != X1 ),
% 3.40/0.96      inference(resolution_lifted,[status(thm)],[c_21,c_31]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_557,plain,
% 3.40/0.96      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.40/0.96      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 3.40/0.96      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.40/0.96      | k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 3.40/0.96      | sK2 != k1_xboole_0 ),
% 3.40/0.96      inference(unflattening,[status(thm)],[c_556]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_1709,plain,
% 3.40/0.96      ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 3.40/0.96      | sK2 != k1_xboole_0
% 3.40/0.96      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.40/0.96      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
% 3.40/0.96      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.40/0.96      inference(predicate_to_equality,[status(thm)],[c_557]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_1918,plain,
% 3.40/0.96      ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 3.40/0.96      | sK2 != k1_xboole_0
% 3.40/0.96      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.40/0.96      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.40/0.96      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.40/0.96      inference(demodulation,[status(thm)],[c_1709,c_6]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_2407,plain,
% 3.40/0.96      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.40/0.96      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.40/0.96      | sK2 != k1_xboole_0
% 3.40/0.96      | k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0 ),
% 3.40/0.96      inference(global_propositional_subsumption,
% 3.40/0.96                [status(thm)],
% 3.40/0.96                [c_1918,c_37,c_39,c_2283]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_2408,plain,
% 3.40/0.96      ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 3.40/0.96      | sK2 != k1_xboole_0
% 3.40/0.96      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.40/0.96      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.40/0.96      inference(renaming,[status(thm)],[c_2407]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_6138,plain,
% 3.40/0.96      ( k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,sK2)) != k1_xboole_0
% 3.40/0.96      | sK2 != k1_xboole_0
% 3.40/0.96      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.40/0.96      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.40/0.96      inference(demodulation,[status(thm)],[c_6134,c_2408]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_6712,plain,
% 3.40/0.96      ( k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,sK2)) != k1_xboole_0
% 3.40/0.96      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.40/0.96      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.40/0.96      inference(global_propositional_subsumption,
% 3.40/0.96                [status(thm)],
% 3.40/0.96                [c_6138,c_6409]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_14374,plain,
% 3.40/0.96      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0
% 3.40/0.96      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
% 3.40/0.96      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.40/0.96      inference(demodulation,[status(thm)],[c_14344,c_6712]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_14444,plain,
% 3.40/0.96      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0
% 3.40/0.96      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.40/0.96      inference(demodulation,[status(thm)],[c_14374,c_5]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_14452,plain,
% 3.40/0.96      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0 ),
% 3.40/0.96      inference(backward_subsumption_resolution,
% 3.40/0.96                [status(thm)],
% 3.40/0.96                [c_14449,c_14444]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_14456,plain,
% 3.40/0.96      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0 ),
% 3.40/0.96      inference(demodulation,[status(thm)],[c_14451,c_14452]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_2937,plain,
% 3.40/0.96      ( v1_relat_1(sK3) = iProver_top ),
% 3.40/0.96      inference(superposition,[status(thm)],[c_1716,c_1723]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_13,plain,
% 3.40/0.96      ( ~ v1_relat_1(X0) | k7_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.40/0.96      inference(cnf_transformation,[],[f64]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_1726,plain,
% 3.40/0.96      ( k7_relat_1(X0,k1_xboole_0) = k1_xboole_0
% 3.40/0.96      | v1_relat_1(X0) != iProver_top ),
% 3.40/0.96      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_3028,plain,
% 3.40/0.96      ( k7_relat_1(sK3,k1_xboole_0) = k1_xboole_0 ),
% 3.40/0.96      inference(superposition,[status(thm)],[c_2937,c_1726]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_14459,plain,
% 3.40/0.96      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
% 3.40/0.96      inference(light_normalisation,[status(thm)],[c_14456,c_3028]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_1730,plain,
% 3.40/0.96      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.40/0.96      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_5006,plain,
% 3.40/0.96      ( k1_relat_1(k7_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 3.40/0.96      | v1_relat_1(X0) != iProver_top ),
% 3.40/0.96      inference(superposition,[status(thm)],[c_1730,c_1725]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_9850,plain,
% 3.40/0.96      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),k1_xboole_0)) = k1_xboole_0 ),
% 3.40/0.96      inference(superposition,[status(thm)],[c_7922,c_5006]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_12,plain,
% 3.40/0.96      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 3.40/0.96      inference(cnf_transformation,[],[f63]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_1727,plain,
% 3.40/0.96      ( v1_relat_1(X0) != iProver_top
% 3.40/0.96      | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
% 3.40/0.96      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_2615,plain,
% 3.40/0.96      ( k7_relat_1(k7_relat_1(X0,X1),k1_xboole_0) = k1_xboole_0
% 3.40/0.96      | v1_relat_1(X0) != iProver_top ),
% 3.40/0.96      inference(superposition,[status(thm)],[c_1727,c_1726]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_3275,plain,
% 3.40/0.96      ( k7_relat_1(k7_relat_1(sK3,X0),k1_xboole_0) = k1_xboole_0 ),
% 3.40/0.96      inference(superposition,[status(thm)],[c_2937,c_2615]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_9852,plain,
% 3.40/0.96      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.40/0.96      inference(light_normalisation,[status(thm)],[c_9850,c_3275]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_6406,plain,
% 3.40/0.96      ( v1_funct_1(k1_xboole_0) = iProver_top ),
% 3.40/0.96      inference(superposition,[status(thm)],[c_3028,c_6143]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_2153,plain,
% 3.40/0.96      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) ),
% 3.40/0.96      inference(instantiation,[status(thm)],[c_4]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_2156,plain,
% 3.40/0.96      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.40/0.96      inference(predicate_to_equality,[status(thm)],[c_2153]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_2158,plain,
% 3.40/0.96      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 3.40/0.96      inference(instantiation,[status(thm)],[c_2156]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_2003,plain,
% 3.40/0.96      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.40/0.96      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
% 3.40/0.96      inference(instantiation,[status(thm)],[c_8]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_2004,plain,
% 3.40/0.96      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.40/0.96      | r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
% 3.40/0.96      inference(predicate_to_equality,[status(thm)],[c_2003]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_2006,plain,
% 3.40/0.96      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
% 3.40/0.96      | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 3.40/0.96      inference(instantiation,[status(thm)],[c_2004]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_23,plain,
% 3.40/0.96      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 3.40/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.40/0.96      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 3.40/0.96      inference(cnf_transformation,[],[f96]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_531,plain,
% 3.40/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.40/0.96      | ~ r1_tarski(k2_relat_1(X2),X3)
% 3.40/0.96      | ~ v1_funct_1(X2)
% 3.40/0.96      | ~ v1_relat_1(X2)
% 3.40/0.96      | X2 != X0
% 3.40/0.96      | X3 != X1
% 3.40/0.96      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 3.40/0.96      | k1_relat_1(X2) != k1_xboole_0 ),
% 3.40/0.96      inference(resolution_lifted,[status(thm)],[c_23,c_29]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_532,plain,
% 3.40/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.40/0.96      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.40/0.96      | ~ v1_funct_1(X0)
% 3.40/0.96      | ~ v1_relat_1(X0)
% 3.40/0.96      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 3.40/0.96      | k1_relat_1(X0) != k1_xboole_0 ),
% 3.40/0.96      inference(unflattening,[status(thm)],[c_531]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_533,plain,
% 3.40/0.96      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
% 3.40/0.96      | k1_relat_1(X1) != k1_xboole_0
% 3.40/0.96      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
% 3.40/0.96      | r1_tarski(k2_relat_1(X1),X0) != iProver_top
% 3.40/0.96      | v1_funct_1(X1) != iProver_top
% 3.40/0.96      | v1_relat_1(X1) != iProver_top ),
% 3.40/0.96      inference(predicate_to_equality,[status(thm)],[c_532]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_535,plain,
% 3.40/0.96      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0
% 3.40/0.96      | k1_relat_1(k1_xboole_0) != k1_xboole_0
% 3.40/0.96      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 3.40/0.96      | r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top
% 3.40/0.96      | v1_funct_1(k1_xboole_0) != iProver_top
% 3.40/0.96      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.40/0.96      inference(instantiation,[status(thm)],[c_533]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_436,plain,
% 3.40/0.96      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.40/0.96      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 3.40/0.96      inference(predicate_to_equality,[status(thm)],[c_435]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_438,plain,
% 3.40/0.96      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 3.40/0.96      | r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0) = iProver_top ),
% 3.40/0.96      inference(instantiation,[status(thm)],[c_436]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_82,plain,
% 3.40/0.96      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.40/0.96      | v1_relat_1(X0) = iProver_top ),
% 3.40/0.96      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(c_84,plain,
% 3.40/0.96      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 3.40/0.96      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.40/0.96      inference(instantiation,[status(thm)],[c_82]) ).
% 3.40/0.96  
% 3.40/0.96  cnf(contradiction,plain,
% 3.40/0.96      ( $false ),
% 3.40/0.96      inference(minisat,
% 3.40/0.96                [status(thm)],
% 3.40/0.96                [c_14459,c_9852,c_6406,c_2158,c_2006,c_535,c_438,c_84]) ).
% 3.40/0.96  
% 3.40/0.96  
% 3.40/0.96  % SZS output end CNFRefutation for theBenchmark.p
% 3.40/0.96  
% 3.40/0.96  ------                               Statistics
% 3.40/0.96  
% 3.40/0.96  ------ General
% 3.40/0.96  
% 3.40/0.96  abstr_ref_over_cycles:                  0
% 3.40/0.96  abstr_ref_under_cycles:                 0
% 3.40/0.96  gc_basic_clause_elim:                   0
% 3.40/0.96  forced_gc_time:                         0
% 3.40/0.96  parsing_time:                           0.01
% 3.40/0.96  unif_index_cands_time:                  0.
% 3.40/0.96  unif_index_add_time:                    0.
% 3.40/0.96  orderings_time:                         0.
% 3.40/0.96  out_proof_time:                         0.014
% 3.40/0.96  total_time:                             0.362
% 3.40/0.96  num_of_symbols:                         49
% 3.40/0.96  num_of_terms:                           11122
% 3.40/0.96  
% 3.40/0.96  ------ Preprocessing
% 3.40/0.96  
% 3.40/0.96  num_of_splits:                          0
% 3.40/0.96  num_of_split_atoms:                     0
% 3.40/0.96  num_of_reused_defs:                     0
% 3.40/0.96  num_eq_ax_congr_red:                    7
% 3.40/0.96  num_of_sem_filtered_clauses:            1
% 3.40/0.96  num_of_subtypes:                        0
% 3.40/0.96  monotx_restored_types:                  0
% 3.40/0.96  sat_num_of_epr_types:                   0
% 3.40/0.96  sat_num_of_non_cyclic_types:            0
% 3.40/0.96  sat_guarded_non_collapsed_types:        0
% 3.40/0.96  num_pure_diseq_elim:                    0
% 3.40/0.96  simp_replaced_by:                       0
% 3.40/0.96  res_preprocessed:                       167
% 3.40/0.96  prep_upred:                             0
% 3.40/0.96  prep_unflattend:                        43
% 3.40/0.96  smt_new_axioms:                         0
% 3.40/0.96  pred_elim_cands:                        4
% 3.40/0.96  pred_elim:                              2
% 3.40/0.96  pred_elim_cl:                           0
% 3.40/0.96  pred_elim_cycles:                       4
% 3.40/0.96  merged_defs:                            8
% 3.40/0.96  merged_defs_ncl:                        0
% 3.40/0.96  bin_hyper_res:                          8
% 3.40/0.96  prep_cycles:                            4
% 3.40/0.96  pred_elim_time:                         0.009
% 3.40/0.96  splitting_time:                         0.
% 3.40/0.96  sem_filter_time:                        0.
% 3.40/0.96  monotx_time:                            0.001
% 3.40/0.96  subtype_inf_time:                       0.
% 3.40/0.96  
% 3.40/0.96  ------ Problem properties
% 3.40/0.96  
% 3.40/0.96  clauses:                                35
% 3.40/0.96  conjectures:                            4
% 3.40/0.96  epr:                                    7
% 3.40/0.96  horn:                                   30
% 3.40/0.96  ground:                                 12
% 3.40/0.96  unary:                                  7
% 3.40/0.96  binary:                                 10
% 3.40/0.96  lits:                                   95
% 3.40/0.96  lits_eq:                                35
% 3.40/0.96  fd_pure:                                0
% 3.40/0.96  fd_pseudo:                              0
% 3.40/0.96  fd_cond:                                3
% 3.40/0.96  fd_pseudo_cond:                         1
% 3.40/0.96  ac_symbols:                             0
% 3.40/0.96  
% 3.40/0.96  ------ Propositional Solver
% 3.40/0.96  
% 3.40/0.96  prop_solver_calls:                      27
% 3.40/0.96  prop_fast_solver_calls:                 1349
% 3.40/0.96  smt_solver_calls:                       0
% 3.40/0.96  smt_fast_solver_calls:                  0
% 3.40/0.96  prop_num_of_clauses:                    5527
% 3.40/0.96  prop_preprocess_simplified:             12324
% 3.40/0.96  prop_fo_subsumed:                       34
% 3.40/0.96  prop_solver_time:                       0.
% 3.40/0.96  smt_solver_time:                        0.
% 3.40/0.96  smt_fast_solver_time:                   0.
% 3.40/0.96  prop_fast_solver_time:                  0.
% 3.40/0.96  prop_unsat_core_time:                   0.
% 3.40/0.96  
% 3.40/0.96  ------ QBF
% 3.40/0.96  
% 3.40/0.96  qbf_q_res:                              0
% 3.40/0.96  qbf_num_tautologies:                    0
% 3.40/0.96  qbf_prep_cycles:                        0
% 3.40/0.96  
% 3.40/0.96  ------ BMC1
% 3.40/0.96  
% 3.40/0.96  bmc1_current_bound:                     -1
% 3.40/0.96  bmc1_last_solved_bound:                 -1
% 3.40/0.96  bmc1_unsat_core_size:                   -1
% 3.40/0.96  bmc1_unsat_core_parents_size:           -1
% 3.40/0.96  bmc1_merge_next_fun:                    0
% 3.40/0.96  bmc1_unsat_core_clauses_time:           0.
% 3.40/0.96  
% 3.40/0.96  ------ Instantiation
% 3.40/0.96  
% 3.40/0.96  inst_num_of_clauses:                    1558
% 3.40/0.96  inst_num_in_passive:                    167
% 3.40/0.96  inst_num_in_active:                     641
% 3.40/0.96  inst_num_in_unprocessed:                751
% 3.40/0.96  inst_num_of_loops:                      680
% 3.40/0.96  inst_num_of_learning_restarts:          0
% 3.40/0.96  inst_num_moves_active_passive:          38
% 3.40/0.96  inst_lit_activity:                      0
% 3.40/0.96  inst_lit_activity_moves:                0
% 3.40/0.96  inst_num_tautologies:                   0
% 3.40/0.96  inst_num_prop_implied:                  0
% 3.40/0.96  inst_num_existing_simplified:           0
% 3.40/0.96  inst_num_eq_res_simplified:             0
% 3.40/0.96  inst_num_child_elim:                    0
% 3.40/0.96  inst_num_of_dismatching_blockings:      577
% 3.40/0.96  inst_num_of_non_proper_insts:           1829
% 3.40/0.96  inst_num_of_duplicates:                 0
% 3.40/0.96  inst_inst_num_from_inst_to_res:         0
% 3.40/0.96  inst_dismatching_checking_time:         0.
% 3.40/0.96  
% 3.40/0.96  ------ Resolution
% 3.40/0.96  
% 3.40/0.96  res_num_of_clauses:                     0
% 3.40/0.96  res_num_in_passive:                     0
% 3.40/0.96  res_num_in_active:                      0
% 3.40/0.96  res_num_of_loops:                       171
% 3.40/0.96  res_forward_subset_subsumed:            85
% 3.40/0.96  res_backward_subset_subsumed:           2
% 3.40/0.96  res_forward_subsumed:                   0
% 3.40/0.96  res_backward_subsumed:                  0
% 3.40/0.96  res_forward_subsumption_resolution:     5
% 3.40/0.96  res_backward_subsumption_resolution:    0
% 3.40/0.96  res_clause_to_clause_subsumption:       932
% 3.40/0.96  res_orphan_elimination:                 0
% 3.40/0.96  res_tautology_del:                      177
% 3.40/0.96  res_num_eq_res_simplified:              1
% 3.40/0.96  res_num_sel_changes:                    0
% 3.40/0.96  res_moves_from_active_to_pass:          0
% 3.40/0.96  
% 3.40/0.96  ------ Superposition
% 3.40/0.96  
% 3.40/0.96  sup_time_total:                         0.
% 3.40/0.96  sup_time_generating:                    0.
% 3.40/0.96  sup_time_sim_full:                      0.
% 3.40/0.96  sup_time_sim_immed:                     0.
% 3.40/0.96  
% 3.40/0.96  sup_num_of_clauses:                     220
% 3.40/0.96  sup_num_in_active:                      70
% 3.40/0.96  sup_num_in_passive:                     150
% 3.40/0.96  sup_num_of_loops:                       134
% 3.40/0.96  sup_fw_superposition:                   167
% 3.40/0.96  sup_bw_superposition:                   174
% 3.40/0.96  sup_immediate_simplified:               92
% 3.40/0.96  sup_given_eliminated:                   1
% 3.40/0.96  comparisons_done:                       0
% 3.40/0.96  comparisons_avoided:                    37
% 3.40/0.96  
% 3.40/0.96  ------ Simplifications
% 3.40/0.96  
% 3.40/0.96  
% 3.40/0.96  sim_fw_subset_subsumed:                 17
% 3.40/0.96  sim_bw_subset_subsumed:                 28
% 3.40/0.96  sim_fw_subsumed:                        25
% 3.40/0.96  sim_bw_subsumed:                        1
% 3.40/0.96  sim_fw_subsumption_res:                 9
% 3.40/0.96  sim_bw_subsumption_res:                 2
% 3.40/0.96  sim_tautology_del:                      6
% 3.40/0.96  sim_eq_tautology_del:                   15
% 3.40/0.96  sim_eq_res_simp:                        4
% 3.40/0.96  sim_fw_demodulated:                     17
% 3.40/0.96  sim_bw_demodulated:                     58
% 3.40/0.96  sim_light_normalised:                   39
% 3.40/0.96  sim_joinable_taut:                      0
% 3.40/0.96  sim_joinable_simp:                      0
% 3.40/0.96  sim_ac_normalised:                      0
% 3.40/0.96  sim_smt_subsumption:                    0
% 3.40/0.96  
%------------------------------------------------------------------------------
