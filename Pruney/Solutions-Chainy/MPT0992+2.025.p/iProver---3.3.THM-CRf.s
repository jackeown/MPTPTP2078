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
% DateTime   : Thu Dec  3 12:03:51 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :  171 (3866 expanded)
%              Number of clauses        :  107 (1323 expanded)
%              Number of leaves         :   14 ( 708 expanded)
%              Depth                    :   27
%              Number of atoms          :  526 (21277 expanded)
%              Number of equality atoms :  260 (5769 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
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

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

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
    inference(ennf_transformation,[],[f18])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

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

fof(f50,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
      | ~ v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK3,sK2)
      | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3)) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 != sK2 )
    & r1_tarski(sK3,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f38,f49])).

fof(f85,plain,(
    r1_tarski(sK3,sK1) ),
    inference(cnf_transformation,[],[f50])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f13])).

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
    inference(flattening,[],[f29])).

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
    inference(nnf_transformation,[],[f30])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f83,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f84,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f50])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f82,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f50])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f87,plain,
    ( ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK3,sK2)
    | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3)) ),
    inference(cnf_transformation,[],[f50])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f63,plain,(
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
    inference(cnf_transformation,[],[f32])).

fof(f86,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f50])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f45])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f91,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f60])).

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

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f90,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f61])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f43])).

fof(f57,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_33,negated_conjecture,
    ( r1_tarski(sK3,sK1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1639,plain,
    ( r1_tarski(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_645,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X0
    | sK2 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_35])).

cnf(c_646,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_645])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_648,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_646,c_34])).

cnf(c_1638,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1644,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2971,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1638,c_1644])).

cnf(c_3023,plain,
    ( k1_relat_1(sK4) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_648,c_2971])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1646,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3318,plain,
    ( k1_relat_1(k7_relat_1(sK4,X0)) = X0
    | sK2 = k1_xboole_0
    | r1_tarski(X0,sK1) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3023,c_1646])).

cnf(c_39,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1917,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1918,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1917])).

cnf(c_3602,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | sK2 = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK4,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3318,c_39,c_1918])).

cnf(c_3603,plain,
    ( k1_relat_1(k7_relat_1(sK4,X0)) = X0
    | sK2 = k1_xboole_0
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_3602])).

cnf(c_3614,plain,
    ( k1_relat_1(k7_relat_1(sK4,sK3)) = sK3
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1639,c_3603])).

cnf(c_28,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1640,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4151,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK3)),X0) != iProver_top
    | v1_funct_1(k7_relat_1(sK4,sK3)) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3614,c_1640])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1641,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4350,plain,
    ( k2_partfun1(sK1,sK2,sK4,X0) = k7_relat_1(sK4,X0)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1638,c_1641])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_37,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_4447,plain,
    ( k2_partfun1(sK1,sK2,sK4,X0) = k7_relat_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4350,c_37])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1642,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4233,plain,
    ( v1_funct_1(k2_partfun1(sK1,sK2,sK4,X0)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1638,c_1642])).

cnf(c_1965,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_partfun1(X0,X1,sK4,X2))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_2360,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_funct_1(k2_partfun1(sK1,sK2,sK4,X0))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1965])).

cnf(c_2361,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_funct_1(k2_partfun1(sK1,sK2,sK4,X0)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2360])).

cnf(c_4388,plain,
    ( v1_funct_1(k2_partfun1(sK1,sK2,sK4,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4233,c_37,c_39,c_2361])).

cnf(c_4456,plain,
    ( v1_funct_1(k7_relat_1(sK4,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4447,c_4388])).

cnf(c_4724,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK3)),X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK3)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4151,c_4456])).

cnf(c_29,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_31,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK3,sK2)
    | ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_656,plain,
    ( ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))
    | ~ v1_relat_1(X0)
    | k2_partfun1(sK1,sK2,sK4,sK3) != X0
    | k1_relat_1(X0) != sK3
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_31])).

cnf(c_657,plain,
    ( ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ r1_tarski(k2_relat_1(k2_partfun1(sK1,sK2,sK4,sK3)),sK2)
    | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))
    | ~ v1_relat_1(k2_partfun1(sK1,sK2,sK4,sK3))
    | k1_relat_1(k2_partfun1(sK1,sK2,sK4,sK3)) != sK3 ),
    inference(unflattening,[status(thm)],[c_656])).

cnf(c_17,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_13,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_371,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_17,c_13])).

cnf(c_375,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_371,c_16])).

cnf(c_376,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_375])).

cnf(c_669,plain,
    ( ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))
    | k1_relat_1(k2_partfun1(sK1,sK2,sK4,sK3)) != sK3 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_657,c_16,c_376])).

cnf(c_1626,plain,
    ( k1_relat_1(k2_partfun1(sK1,sK2,sK4,sK3)) != sK3
    | m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_669])).

cnf(c_4454,plain,
    ( k1_relat_1(k7_relat_1(sK4,sK3)) != sK3
    | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_1(k7_relat_1(sK4,sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4447,c_1626])).

cnf(c_4470,plain,
    ( k1_relat_1(k7_relat_1(sK4,sK3)) != sK3
    | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4454,c_4456])).

cnf(c_4880,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3614,c_4470])).

cnf(c_5399,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK3)),sK2) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4724,c_4880])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1643,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4886,plain,
    ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4447,c_1643])).

cnf(c_5402,plain,
    ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4886,c_37,c_39])).

cnf(c_1645,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_5411,plain,
    ( v1_relat_1(k7_relat_1(sK4,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5402,c_1645])).

cnf(c_1635,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_376])).

cnf(c_5410,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK4,X0)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_5402,c_1635])).

cnf(c_5917,plain,
    ( sK2 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5399,c_5411,c_5410])).

cnf(c_5413,plain,
    ( k1_relset_1(sK1,sK2,k7_relat_1(sK4,X0)) = k1_relat_1(k7_relat_1(sK4,X0)) ),
    inference(superposition,[status(thm)],[c_5402,c_1644])).

cnf(c_5919,plain,
    ( k1_relset_1(sK1,k1_xboole_0,k7_relat_1(sK4,X0)) = k1_relat_1(k7_relat_1(sK4,X0)) ),
    inference(demodulation,[status(thm)],[c_5917,c_5413])).

cnf(c_32,negated_conjecture,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_5936,plain,
    ( sK1 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5917,c_32])).

cnf(c_5937,plain,
    ( sK1 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_5936])).

cnf(c_6009,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK4,X0)) = k1_relat_1(k7_relat_1(sK4,X0)) ),
    inference(light_normalisation,[status(thm)],[c_5919,c_5937])).

cnf(c_5921,plain,
    ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5917,c_5402])).

cnf(c_5988,plain,
    ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5921,c_5937])).

cnf(c_9,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_5990,plain,
    ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5988,c_9])).

cnf(c_21,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_570,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))
    | k2_partfun1(sK1,sK2,sK4,sK3) != X0
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | sK3 != k1_xboole_0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_31])).

cnf(c_571,plain,
    ( ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))
    | k1_relset_1(k1_xboole_0,sK2,k2_partfun1(sK1,sK2,sK4,sK3)) != k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_570])).

cnf(c_1630,plain,
    ( k1_relset_1(k1_xboole_0,sK2,k2_partfun1(sK1,sK2,sK4,sK3)) != k1_xboole_0
    | sK3 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top
    | v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_571])).

cnf(c_1834,plain,
    ( k1_relset_1(k1_xboole_0,sK2,k2_partfun1(sK1,sK2,sK4,sK3)) != k1_xboole_0
    | sK3 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1630,c_9])).

cnf(c_2094,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1965])).

cnf(c_2095,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2094])).

cnf(c_2366,plain,
    ( m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | sK3 != k1_xboole_0
    | k1_relset_1(k1_xboole_0,sK2,k2_partfun1(sK1,sK2,sK4,sK3)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1834,c_37,c_39,c_2095])).

cnf(c_2367,plain,
    ( k1_relset_1(k1_xboole_0,sK2,k2_partfun1(sK1,sK2,sK4,sK3)) != k1_xboole_0
    | sK3 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2366])).

cnf(c_4451,plain,
    ( k1_relset_1(k1_xboole_0,sK2,k7_relat_1(sK4,sK3)) != k1_xboole_0
    | sK3 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4447,c_2367])).

cnf(c_5923,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK4,sK3)) != k1_xboole_0
    | sK3 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) != iProver_top
    | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5917,c_4451])).

cnf(c_8,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_5979,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK4,sK3)) != k1_xboole_0
    | sK3 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5923,c_8])).

cnf(c_5992,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK4,sK3)) != k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_5990,c_5979])).

cnf(c_6011,plain,
    ( k1_relat_1(k7_relat_1(sK4,sK3)) != k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6009,c_5992])).

cnf(c_7,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2961,plain,
    ( r1_tarski(k1_xboole_0,sK3) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2962,plain,
    ( r1_tarski(k1_xboole_0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2961])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1650,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3125,plain,
    ( sK3 = sK1
    | r1_tarski(sK1,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1639,c_1650])).

cnf(c_6037,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5937,c_3125])).

cnf(c_7348,plain,
    ( k1_relat_1(k7_relat_1(sK4,sK3)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6011,c_2962,c_6037])).

cnf(c_1648,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3612,plain,
    ( k1_relat_1(k7_relat_1(sK4,k1_xboole_0)) = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1648,c_3603])).

cnf(c_1993,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | k1_relat_1(k7_relat_1(sK4,X0)) = X0 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1995,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | k1_relat_1(k7_relat_1(sK4,k1_xboole_0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1993])).

cnf(c_2313,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_4027,plain,
    ( k1_relat_1(k7_relat_1(sK4,k1_xboole_0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3612,c_34,c_1917,c_1995,c_2313])).

cnf(c_7138,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6037,c_2962])).

cnf(c_7350,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7348,c_4027,c_7138])).

cnf(c_7351,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_7350])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:13:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.32/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/0.98  
% 3.32/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.32/0.98  
% 3.32/0.98  ------  iProver source info
% 3.32/0.98  
% 3.32/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.32/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.32/0.98  git: non_committed_changes: false
% 3.32/0.98  git: last_make_outside_of_git: false
% 3.32/0.98  
% 3.32/0.98  ------ 
% 3.32/0.98  
% 3.32/0.98  ------ Input Options
% 3.32/0.98  
% 3.32/0.98  --out_options                           all
% 3.32/0.98  --tptp_safe_out                         true
% 3.32/0.98  --problem_path                          ""
% 3.32/0.98  --include_path                          ""
% 3.32/0.98  --clausifier                            res/vclausify_rel
% 3.32/0.98  --clausifier_options                    --mode clausify
% 3.32/0.98  --stdin                                 false
% 3.32/0.98  --stats_out                             all
% 3.32/0.98  
% 3.32/0.98  ------ General Options
% 3.32/0.98  
% 3.32/0.98  --fof                                   false
% 3.32/0.98  --time_out_real                         305.
% 3.32/0.98  --time_out_virtual                      -1.
% 3.32/0.98  --symbol_type_check                     false
% 3.32/0.98  --clausify_out                          false
% 3.32/0.98  --sig_cnt_out                           false
% 3.32/0.98  --trig_cnt_out                          false
% 3.32/0.98  --trig_cnt_out_tolerance                1.
% 3.32/0.98  --trig_cnt_out_sk_spl                   false
% 3.32/0.98  --abstr_cl_out                          false
% 3.32/0.98  
% 3.32/0.98  ------ Global Options
% 3.32/0.98  
% 3.32/0.98  --schedule                              default
% 3.32/0.98  --add_important_lit                     false
% 3.32/0.98  --prop_solver_per_cl                    1000
% 3.32/0.98  --min_unsat_core                        false
% 3.32/0.98  --soft_assumptions                      false
% 3.32/0.98  --soft_lemma_size                       3
% 3.32/0.98  --prop_impl_unit_size                   0
% 3.32/0.98  --prop_impl_unit                        []
% 3.32/0.98  --share_sel_clauses                     true
% 3.32/0.98  --reset_solvers                         false
% 3.32/0.98  --bc_imp_inh                            [conj_cone]
% 3.32/0.98  --conj_cone_tolerance                   3.
% 3.32/0.98  --extra_neg_conj                        none
% 3.32/0.98  --large_theory_mode                     true
% 3.32/0.98  --prolific_symb_bound                   200
% 3.32/0.98  --lt_threshold                          2000
% 3.32/0.98  --clause_weak_htbl                      true
% 3.32/0.98  --gc_record_bc_elim                     false
% 3.32/0.98  
% 3.32/0.98  ------ Preprocessing Options
% 3.32/0.98  
% 3.32/0.98  --preprocessing_flag                    true
% 3.32/0.98  --time_out_prep_mult                    0.1
% 3.32/0.98  --splitting_mode                        input
% 3.32/0.98  --splitting_grd                         true
% 3.32/0.98  --splitting_cvd                         false
% 3.32/0.98  --splitting_cvd_svl                     false
% 3.32/0.98  --splitting_nvd                         32
% 3.32/0.98  --sub_typing                            true
% 3.32/0.98  --prep_gs_sim                           true
% 3.32/0.98  --prep_unflatten                        true
% 3.32/0.98  --prep_res_sim                          true
% 3.32/0.98  --prep_upred                            true
% 3.32/0.98  --prep_sem_filter                       exhaustive
% 3.32/0.98  --prep_sem_filter_out                   false
% 3.32/0.98  --pred_elim                             true
% 3.32/0.98  --res_sim_input                         true
% 3.32/0.98  --eq_ax_congr_red                       true
% 3.32/0.98  --pure_diseq_elim                       true
% 3.32/0.98  --brand_transform                       false
% 3.32/0.98  --non_eq_to_eq                          false
% 3.32/0.98  --prep_def_merge                        true
% 3.32/0.98  --prep_def_merge_prop_impl              false
% 3.32/0.98  --prep_def_merge_mbd                    true
% 3.32/0.98  --prep_def_merge_tr_red                 false
% 3.32/0.98  --prep_def_merge_tr_cl                  false
% 3.32/0.98  --smt_preprocessing                     true
% 3.32/0.98  --smt_ac_axioms                         fast
% 3.32/0.98  --preprocessed_out                      false
% 3.32/0.98  --preprocessed_stats                    false
% 3.32/0.98  
% 3.32/0.98  ------ Abstraction refinement Options
% 3.32/0.98  
% 3.32/0.98  --abstr_ref                             []
% 3.32/0.98  --abstr_ref_prep                        false
% 3.32/0.98  --abstr_ref_until_sat                   false
% 3.32/0.98  --abstr_ref_sig_restrict                funpre
% 3.32/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.32/0.98  --abstr_ref_under                       []
% 3.32/0.98  
% 3.32/0.98  ------ SAT Options
% 3.32/0.98  
% 3.32/0.98  --sat_mode                              false
% 3.32/0.98  --sat_fm_restart_options                ""
% 3.32/0.98  --sat_gr_def                            false
% 3.32/0.98  --sat_epr_types                         true
% 3.32/0.98  --sat_non_cyclic_types                  false
% 3.32/0.98  --sat_finite_models                     false
% 3.32/0.98  --sat_fm_lemmas                         false
% 3.32/0.98  --sat_fm_prep                           false
% 3.32/0.98  --sat_fm_uc_incr                        true
% 3.32/0.98  --sat_out_model                         small
% 3.32/0.98  --sat_out_clauses                       false
% 3.32/0.98  
% 3.32/0.98  ------ QBF Options
% 3.32/0.98  
% 3.32/0.98  --qbf_mode                              false
% 3.32/0.98  --qbf_elim_univ                         false
% 3.32/0.98  --qbf_dom_inst                          none
% 3.32/0.98  --qbf_dom_pre_inst                      false
% 3.32/0.98  --qbf_sk_in                             false
% 3.32/0.98  --qbf_pred_elim                         true
% 3.32/0.98  --qbf_split                             512
% 3.32/0.98  
% 3.32/0.98  ------ BMC1 Options
% 3.32/0.98  
% 3.32/0.98  --bmc1_incremental                      false
% 3.32/0.98  --bmc1_axioms                           reachable_all
% 3.32/0.98  --bmc1_min_bound                        0
% 3.32/0.98  --bmc1_max_bound                        -1
% 3.32/0.98  --bmc1_max_bound_default                -1
% 3.32/0.98  --bmc1_symbol_reachability              true
% 3.32/0.98  --bmc1_property_lemmas                  false
% 3.32/0.98  --bmc1_k_induction                      false
% 3.32/0.98  --bmc1_non_equiv_states                 false
% 3.32/0.98  --bmc1_deadlock                         false
% 3.32/0.98  --bmc1_ucm                              false
% 3.32/0.98  --bmc1_add_unsat_core                   none
% 3.32/0.98  --bmc1_unsat_core_children              false
% 3.32/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.32/0.98  --bmc1_out_stat                         full
% 3.32/0.98  --bmc1_ground_init                      false
% 3.32/0.98  --bmc1_pre_inst_next_state              false
% 3.32/0.98  --bmc1_pre_inst_state                   false
% 3.32/0.98  --bmc1_pre_inst_reach_state             false
% 3.32/0.98  --bmc1_out_unsat_core                   false
% 3.32/0.98  --bmc1_aig_witness_out                  false
% 3.32/0.98  --bmc1_verbose                          false
% 3.32/0.98  --bmc1_dump_clauses_tptp                false
% 3.32/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.32/0.98  --bmc1_dump_file                        -
% 3.32/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.32/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.32/0.98  --bmc1_ucm_extend_mode                  1
% 3.32/0.98  --bmc1_ucm_init_mode                    2
% 3.32/0.98  --bmc1_ucm_cone_mode                    none
% 3.32/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.32/0.98  --bmc1_ucm_relax_model                  4
% 3.32/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.32/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.32/0.98  --bmc1_ucm_layered_model                none
% 3.32/0.98  --bmc1_ucm_max_lemma_size               10
% 3.32/0.98  
% 3.32/0.98  ------ AIG Options
% 3.32/0.98  
% 3.32/0.98  --aig_mode                              false
% 3.32/0.98  
% 3.32/0.98  ------ Instantiation Options
% 3.32/0.98  
% 3.32/0.98  --instantiation_flag                    true
% 3.32/0.98  --inst_sos_flag                         false
% 3.32/0.98  --inst_sos_phase                        true
% 3.32/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.32/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.32/0.98  --inst_lit_sel_side                     num_symb
% 3.32/0.98  --inst_solver_per_active                1400
% 3.32/0.98  --inst_solver_calls_frac                1.
% 3.32/0.98  --inst_passive_queue_type               priority_queues
% 3.32/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.32/0.98  --inst_passive_queues_freq              [25;2]
% 3.32/0.98  --inst_dismatching                      true
% 3.32/0.98  --inst_eager_unprocessed_to_passive     true
% 3.32/0.98  --inst_prop_sim_given                   true
% 3.32/0.98  --inst_prop_sim_new                     false
% 3.32/0.98  --inst_subs_new                         false
% 3.32/0.98  --inst_eq_res_simp                      false
% 3.32/0.98  --inst_subs_given                       false
% 3.32/0.98  --inst_orphan_elimination               true
% 3.32/0.98  --inst_learning_loop_flag               true
% 3.32/0.98  --inst_learning_start                   3000
% 3.32/0.98  --inst_learning_factor                  2
% 3.32/0.98  --inst_start_prop_sim_after_learn       3
% 3.32/0.98  --inst_sel_renew                        solver
% 3.32/0.98  --inst_lit_activity_flag                true
% 3.32/0.98  --inst_restr_to_given                   false
% 3.32/0.98  --inst_activity_threshold               500
% 3.32/0.98  --inst_out_proof                        true
% 3.32/0.98  
% 3.32/0.98  ------ Resolution Options
% 3.32/0.98  
% 3.32/0.98  --resolution_flag                       true
% 3.32/0.98  --res_lit_sel                           adaptive
% 3.32/0.98  --res_lit_sel_side                      none
% 3.32/0.98  --res_ordering                          kbo
% 3.32/0.98  --res_to_prop_solver                    active
% 3.32/0.98  --res_prop_simpl_new                    false
% 3.32/0.98  --res_prop_simpl_given                  true
% 3.32/0.98  --res_passive_queue_type                priority_queues
% 3.32/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.32/0.98  --res_passive_queues_freq               [15;5]
% 3.32/0.98  --res_forward_subs                      full
% 3.32/0.98  --res_backward_subs                     full
% 3.32/0.98  --res_forward_subs_resolution           true
% 3.32/0.98  --res_backward_subs_resolution          true
% 3.32/0.98  --res_orphan_elimination                true
% 3.32/0.98  --res_time_limit                        2.
% 3.32/0.98  --res_out_proof                         true
% 3.32/0.98  
% 3.32/0.98  ------ Superposition Options
% 3.32/0.98  
% 3.32/0.98  --superposition_flag                    true
% 3.32/0.98  --sup_passive_queue_type                priority_queues
% 3.32/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.32/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.32/0.98  --demod_completeness_check              fast
% 3.32/0.98  --demod_use_ground                      true
% 3.32/0.98  --sup_to_prop_solver                    passive
% 3.32/0.98  --sup_prop_simpl_new                    true
% 3.32/0.98  --sup_prop_simpl_given                  true
% 3.32/0.98  --sup_fun_splitting                     false
% 3.32/0.98  --sup_smt_interval                      50000
% 3.32/0.98  
% 3.32/0.98  ------ Superposition Simplification Setup
% 3.32/0.98  
% 3.32/0.98  --sup_indices_passive                   []
% 3.32/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.32/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/0.98  --sup_full_bw                           [BwDemod]
% 3.32/0.98  --sup_immed_triv                        [TrivRules]
% 3.32/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.32/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/0.98  --sup_immed_bw_main                     []
% 3.32/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.32/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.32/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.32/0.98  
% 3.32/0.98  ------ Combination Options
% 3.32/0.98  
% 3.32/0.98  --comb_res_mult                         3
% 3.32/0.98  --comb_sup_mult                         2
% 3.32/0.98  --comb_inst_mult                        10
% 3.32/0.98  
% 3.32/0.98  ------ Debug Options
% 3.32/0.98  
% 3.32/0.98  --dbg_backtrace                         false
% 3.32/0.98  --dbg_dump_prop_clauses                 false
% 3.32/0.98  --dbg_dump_prop_clauses_file            -
% 3.32/0.98  --dbg_out_stat                          false
% 3.32/0.98  ------ Parsing...
% 3.32/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.32/0.98  
% 3.32/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.32/0.98  
% 3.32/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.32/0.98  
% 3.32/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.32/0.98  ------ Proving...
% 3.32/0.98  ------ Problem Properties 
% 3.32/0.98  
% 3.32/0.98  
% 3.32/0.98  clauses                                 34
% 3.32/0.98  conjectures                             4
% 3.32/0.98  EPR                                     7
% 3.32/0.98  Horn                                    28
% 3.32/0.98  unary                                   7
% 3.32/0.98  binary                                  9
% 3.32/0.98  lits                                    93
% 3.32/0.98  lits eq                                 34
% 3.32/0.98  fd_pure                                 0
% 3.32/0.98  fd_pseudo                               0
% 3.32/0.98  fd_cond                                 3
% 3.32/0.98  fd_pseudo_cond                          1
% 3.32/0.98  AC symbols                              0
% 3.32/0.98  
% 3.32/0.98  ------ Schedule dynamic 5 is on 
% 3.32/0.98  
% 3.32/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.32/0.98  
% 3.32/0.98  
% 3.32/0.98  ------ 
% 3.32/0.98  Current options:
% 3.32/0.98  ------ 
% 3.32/0.98  
% 3.32/0.98  ------ Input Options
% 3.32/0.98  
% 3.32/0.98  --out_options                           all
% 3.32/0.98  --tptp_safe_out                         true
% 3.32/0.98  --problem_path                          ""
% 3.32/0.98  --include_path                          ""
% 3.32/0.98  --clausifier                            res/vclausify_rel
% 3.32/0.98  --clausifier_options                    --mode clausify
% 3.32/0.98  --stdin                                 false
% 3.32/0.98  --stats_out                             all
% 3.32/0.98  
% 3.32/0.98  ------ General Options
% 3.32/0.98  
% 3.32/0.98  --fof                                   false
% 3.32/0.98  --time_out_real                         305.
% 3.32/0.98  --time_out_virtual                      -1.
% 3.32/0.98  --symbol_type_check                     false
% 3.32/0.98  --clausify_out                          false
% 3.32/0.98  --sig_cnt_out                           false
% 3.32/0.98  --trig_cnt_out                          false
% 3.32/0.98  --trig_cnt_out_tolerance                1.
% 3.32/0.98  --trig_cnt_out_sk_spl                   false
% 3.32/0.98  --abstr_cl_out                          false
% 3.32/0.98  
% 3.32/0.98  ------ Global Options
% 3.32/0.98  
% 3.32/0.98  --schedule                              default
% 3.32/0.98  --add_important_lit                     false
% 3.32/0.98  --prop_solver_per_cl                    1000
% 3.32/0.98  --min_unsat_core                        false
% 3.32/0.98  --soft_assumptions                      false
% 3.32/0.98  --soft_lemma_size                       3
% 3.32/0.98  --prop_impl_unit_size                   0
% 3.32/0.98  --prop_impl_unit                        []
% 3.32/0.98  --share_sel_clauses                     true
% 3.32/0.98  --reset_solvers                         false
% 3.32/0.98  --bc_imp_inh                            [conj_cone]
% 3.32/0.98  --conj_cone_tolerance                   3.
% 3.32/0.98  --extra_neg_conj                        none
% 3.32/0.98  --large_theory_mode                     true
% 3.32/0.98  --prolific_symb_bound                   200
% 3.32/0.98  --lt_threshold                          2000
% 3.32/0.98  --clause_weak_htbl                      true
% 3.32/0.98  --gc_record_bc_elim                     false
% 3.32/0.98  
% 3.32/0.98  ------ Preprocessing Options
% 3.32/0.98  
% 3.32/0.98  --preprocessing_flag                    true
% 3.32/0.98  --time_out_prep_mult                    0.1
% 3.32/0.98  --splitting_mode                        input
% 3.32/0.98  --splitting_grd                         true
% 3.32/0.98  --splitting_cvd                         false
% 3.32/0.98  --splitting_cvd_svl                     false
% 3.32/0.98  --splitting_nvd                         32
% 3.32/0.98  --sub_typing                            true
% 3.32/0.98  --prep_gs_sim                           true
% 3.32/0.98  --prep_unflatten                        true
% 3.32/0.98  --prep_res_sim                          true
% 3.32/0.98  --prep_upred                            true
% 3.32/0.98  --prep_sem_filter                       exhaustive
% 3.32/0.98  --prep_sem_filter_out                   false
% 3.32/0.98  --pred_elim                             true
% 3.32/0.98  --res_sim_input                         true
% 3.32/0.98  --eq_ax_congr_red                       true
% 3.32/0.98  --pure_diseq_elim                       true
% 3.32/0.98  --brand_transform                       false
% 3.32/0.98  --non_eq_to_eq                          false
% 3.32/0.98  --prep_def_merge                        true
% 3.32/0.98  --prep_def_merge_prop_impl              false
% 3.32/0.98  --prep_def_merge_mbd                    true
% 3.32/0.98  --prep_def_merge_tr_red                 false
% 3.32/0.98  --prep_def_merge_tr_cl                  false
% 3.32/0.98  --smt_preprocessing                     true
% 3.32/0.98  --smt_ac_axioms                         fast
% 3.32/0.98  --preprocessed_out                      false
% 3.32/0.98  --preprocessed_stats                    false
% 3.32/0.98  
% 3.32/0.98  ------ Abstraction refinement Options
% 3.32/0.98  
% 3.32/0.98  --abstr_ref                             []
% 3.32/0.98  --abstr_ref_prep                        false
% 3.32/0.98  --abstr_ref_until_sat                   false
% 3.32/0.98  --abstr_ref_sig_restrict                funpre
% 3.32/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.32/0.98  --abstr_ref_under                       []
% 3.32/0.98  
% 3.32/0.98  ------ SAT Options
% 3.32/0.98  
% 3.32/0.98  --sat_mode                              false
% 3.32/0.98  --sat_fm_restart_options                ""
% 3.32/0.98  --sat_gr_def                            false
% 3.32/0.98  --sat_epr_types                         true
% 3.32/0.98  --sat_non_cyclic_types                  false
% 3.32/0.98  --sat_finite_models                     false
% 3.32/0.98  --sat_fm_lemmas                         false
% 3.32/0.98  --sat_fm_prep                           false
% 3.32/0.98  --sat_fm_uc_incr                        true
% 3.32/0.98  --sat_out_model                         small
% 3.32/0.98  --sat_out_clauses                       false
% 3.32/0.98  
% 3.32/0.98  ------ QBF Options
% 3.32/0.98  
% 3.32/0.98  --qbf_mode                              false
% 3.32/0.98  --qbf_elim_univ                         false
% 3.32/0.98  --qbf_dom_inst                          none
% 3.32/0.98  --qbf_dom_pre_inst                      false
% 3.32/0.98  --qbf_sk_in                             false
% 3.32/0.98  --qbf_pred_elim                         true
% 3.32/0.98  --qbf_split                             512
% 3.32/0.98  
% 3.32/0.98  ------ BMC1 Options
% 3.32/0.98  
% 3.32/0.98  --bmc1_incremental                      false
% 3.32/0.98  --bmc1_axioms                           reachable_all
% 3.32/0.98  --bmc1_min_bound                        0
% 3.32/0.98  --bmc1_max_bound                        -1
% 3.32/0.98  --bmc1_max_bound_default                -1
% 3.32/0.98  --bmc1_symbol_reachability              true
% 3.32/0.98  --bmc1_property_lemmas                  false
% 3.32/0.98  --bmc1_k_induction                      false
% 3.32/0.98  --bmc1_non_equiv_states                 false
% 3.32/0.98  --bmc1_deadlock                         false
% 3.32/0.98  --bmc1_ucm                              false
% 3.32/0.98  --bmc1_add_unsat_core                   none
% 3.32/0.98  --bmc1_unsat_core_children              false
% 3.32/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.32/0.98  --bmc1_out_stat                         full
% 3.32/0.98  --bmc1_ground_init                      false
% 3.32/0.98  --bmc1_pre_inst_next_state              false
% 3.32/0.98  --bmc1_pre_inst_state                   false
% 3.32/0.98  --bmc1_pre_inst_reach_state             false
% 3.32/0.98  --bmc1_out_unsat_core                   false
% 3.32/0.98  --bmc1_aig_witness_out                  false
% 3.32/0.98  --bmc1_verbose                          false
% 3.32/0.98  --bmc1_dump_clauses_tptp                false
% 3.32/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.32/0.98  --bmc1_dump_file                        -
% 3.32/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.32/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.32/0.98  --bmc1_ucm_extend_mode                  1
% 3.32/0.98  --bmc1_ucm_init_mode                    2
% 3.32/0.98  --bmc1_ucm_cone_mode                    none
% 3.32/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.32/0.98  --bmc1_ucm_relax_model                  4
% 3.32/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.32/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.32/0.98  --bmc1_ucm_layered_model                none
% 3.32/0.98  --bmc1_ucm_max_lemma_size               10
% 3.32/0.98  
% 3.32/0.98  ------ AIG Options
% 3.32/0.98  
% 3.32/0.98  --aig_mode                              false
% 3.32/0.98  
% 3.32/0.98  ------ Instantiation Options
% 3.32/0.98  
% 3.32/0.98  --instantiation_flag                    true
% 3.32/0.98  --inst_sos_flag                         false
% 3.32/0.98  --inst_sos_phase                        true
% 3.32/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.32/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.32/0.98  --inst_lit_sel_side                     none
% 3.32/0.98  --inst_solver_per_active                1400
% 3.32/0.98  --inst_solver_calls_frac                1.
% 3.32/0.98  --inst_passive_queue_type               priority_queues
% 3.32/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.32/0.98  --inst_passive_queues_freq              [25;2]
% 3.32/0.98  --inst_dismatching                      true
% 3.32/0.98  --inst_eager_unprocessed_to_passive     true
% 3.32/0.98  --inst_prop_sim_given                   true
% 3.32/0.98  --inst_prop_sim_new                     false
% 3.32/0.98  --inst_subs_new                         false
% 3.32/0.98  --inst_eq_res_simp                      false
% 3.32/0.98  --inst_subs_given                       false
% 3.32/0.98  --inst_orphan_elimination               true
% 3.32/0.98  --inst_learning_loop_flag               true
% 3.32/0.98  --inst_learning_start                   3000
% 3.32/0.98  --inst_learning_factor                  2
% 3.32/0.98  --inst_start_prop_sim_after_learn       3
% 3.32/0.98  --inst_sel_renew                        solver
% 3.32/0.98  --inst_lit_activity_flag                true
% 3.32/0.98  --inst_restr_to_given                   false
% 3.32/0.98  --inst_activity_threshold               500
% 3.32/0.98  --inst_out_proof                        true
% 3.32/0.98  
% 3.32/0.98  ------ Resolution Options
% 3.32/0.98  
% 3.32/0.98  --resolution_flag                       false
% 3.32/0.98  --res_lit_sel                           adaptive
% 3.32/0.98  --res_lit_sel_side                      none
% 3.32/0.98  --res_ordering                          kbo
% 3.32/0.98  --res_to_prop_solver                    active
% 3.32/0.98  --res_prop_simpl_new                    false
% 3.32/0.98  --res_prop_simpl_given                  true
% 3.32/0.98  --res_passive_queue_type                priority_queues
% 3.32/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.32/0.98  --res_passive_queues_freq               [15;5]
% 3.32/0.98  --res_forward_subs                      full
% 3.32/0.98  --res_backward_subs                     full
% 3.32/0.98  --res_forward_subs_resolution           true
% 3.32/0.98  --res_backward_subs_resolution          true
% 3.32/0.98  --res_orphan_elimination                true
% 3.32/0.98  --res_time_limit                        2.
% 3.32/0.98  --res_out_proof                         true
% 3.32/0.98  
% 3.32/0.98  ------ Superposition Options
% 3.32/0.98  
% 3.32/0.98  --superposition_flag                    true
% 3.32/0.98  --sup_passive_queue_type                priority_queues
% 3.32/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.32/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.32/0.98  --demod_completeness_check              fast
% 3.32/0.98  --demod_use_ground                      true
% 3.32/0.98  --sup_to_prop_solver                    passive
% 3.32/0.98  --sup_prop_simpl_new                    true
% 3.32/0.98  --sup_prop_simpl_given                  true
% 3.32/0.98  --sup_fun_splitting                     false
% 3.32/0.98  --sup_smt_interval                      50000
% 3.32/0.98  
% 3.32/0.98  ------ Superposition Simplification Setup
% 3.32/0.98  
% 3.32/0.98  --sup_indices_passive                   []
% 3.32/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.32/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/0.98  --sup_full_bw                           [BwDemod]
% 3.32/0.98  --sup_immed_triv                        [TrivRules]
% 3.32/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.32/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/0.98  --sup_immed_bw_main                     []
% 3.32/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.32/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.32/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.32/0.98  
% 3.32/0.98  ------ Combination Options
% 3.32/0.98  
% 3.32/0.98  --comb_res_mult                         3
% 3.32/0.98  --comb_sup_mult                         2
% 3.32/0.98  --comb_inst_mult                        10
% 3.32/0.98  
% 3.32/0.98  ------ Debug Options
% 3.32/0.98  
% 3.32/0.98  --dbg_backtrace                         false
% 3.32/0.98  --dbg_dump_prop_clauses                 false
% 3.32/0.98  --dbg_dump_prop_clauses_file            -
% 3.32/0.98  --dbg_out_stat                          false
% 3.32/0.98  
% 3.32/0.98  
% 3.32/0.98  
% 3.32/0.98  
% 3.32/0.98  ------ Proving...
% 3.32/0.98  
% 3.32/0.98  
% 3.32/0.98  % SZS status Theorem for theBenchmark.p
% 3.32/0.98  
% 3.32/0.98   Resolution empty clause
% 3.32/0.98  
% 3.32/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.32/0.98  
% 3.32/0.98  fof(f17,conjecture,(
% 3.32/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.32/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/0.98  
% 3.32/0.98  fof(f18,negated_conjecture,(
% 3.32/0.98    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.32/0.98    inference(negated_conjecture,[],[f17])).
% 3.32/0.98  
% 3.32/0.98  fof(f37,plain,(
% 3.32/0.98    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.32/0.98    inference(ennf_transformation,[],[f18])).
% 3.32/0.98  
% 3.32/0.98  fof(f38,plain,(
% 3.32/0.98    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.32/0.98    inference(flattening,[],[f37])).
% 3.32/0.98  
% 3.32/0.98  fof(f49,plain,(
% 3.32/0.98    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK3,sK2) | ~v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & r1_tarski(sK3,sK1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4))),
% 3.32/0.98    introduced(choice_axiom,[])).
% 3.32/0.98  
% 3.32/0.98  fof(f50,plain,(
% 3.32/0.98    (~m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK3,sK2) | ~v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & r1_tarski(sK3,sK1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)),
% 3.32/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f38,f49])).
% 3.32/0.98  
% 3.32/0.98  fof(f85,plain,(
% 3.32/0.98    r1_tarski(sK3,sK1)),
% 3.32/0.98    inference(cnf_transformation,[],[f50])).
% 3.32/0.98  
% 3.32/0.98  fof(f13,axiom,(
% 3.32/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.32/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f29,plain,(
% 3.32/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.32/0.99    inference(ennf_transformation,[],[f13])).
% 3.32/0.99  
% 3.32/0.99  fof(f30,plain,(
% 3.32/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.32/0.99    inference(flattening,[],[f29])).
% 3.32/0.99  
% 3.32/0.99  fof(f48,plain,(
% 3.32/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.32/0.99    inference(nnf_transformation,[],[f30])).
% 3.32/0.99  
% 3.32/0.99  fof(f70,plain,(
% 3.32/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.32/0.99    inference(cnf_transformation,[],[f48])).
% 3.32/0.99  
% 3.32/0.99  fof(f83,plain,(
% 3.32/0.99    v1_funct_2(sK4,sK1,sK2)),
% 3.32/0.99    inference(cnf_transformation,[],[f50])).
% 3.32/0.99  
% 3.32/0.99  fof(f84,plain,(
% 3.32/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 3.32/0.99    inference(cnf_transformation,[],[f50])).
% 3.32/0.99  
% 3.32/0.99  fof(f12,axiom,(
% 3.32/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.32/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f28,plain,(
% 3.32/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.32/0.99    inference(ennf_transformation,[],[f12])).
% 3.32/0.99  
% 3.32/0.99  fof(f69,plain,(
% 3.32/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.32/0.99    inference(cnf_transformation,[],[f28])).
% 3.32/0.99  
% 3.32/0.99  fof(f9,axiom,(
% 3.32/0.99    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 3.32/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f24,plain,(
% 3.32/0.99    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 3.32/0.99    inference(ennf_transformation,[],[f9])).
% 3.32/0.99  
% 3.32/0.99  fof(f25,plain,(
% 3.32/0.99    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.32/0.99    inference(flattening,[],[f24])).
% 3.32/0.99  
% 3.32/0.99  fof(f66,plain,(
% 3.32/0.99    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f25])).
% 3.32/0.99  
% 3.32/0.99  fof(f10,axiom,(
% 3.32/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.32/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f26,plain,(
% 3.32/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.32/0.99    inference(ennf_transformation,[],[f10])).
% 3.32/0.99  
% 3.32/0.99  fof(f67,plain,(
% 3.32/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.32/0.99    inference(cnf_transformation,[],[f26])).
% 3.32/0.99  
% 3.32/0.99  fof(f16,axiom,(
% 3.32/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 3.32/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f35,plain,(
% 3.32/0.99    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.32/0.99    inference(ennf_transformation,[],[f16])).
% 3.32/0.99  
% 3.32/0.99  fof(f36,plain,(
% 3.32/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.32/0.99    inference(flattening,[],[f35])).
% 3.32/0.99  
% 3.32/0.99  fof(f81,plain,(
% 3.32/0.99    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f36])).
% 3.32/0.99  
% 3.32/0.99  fof(f15,axiom,(
% 3.32/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 3.32/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f33,plain,(
% 3.32/0.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.32/0.99    inference(ennf_transformation,[],[f15])).
% 3.32/0.99  
% 3.32/0.99  fof(f34,plain,(
% 3.32/0.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.32/0.99    inference(flattening,[],[f33])).
% 3.32/0.99  
% 3.32/0.99  fof(f78,plain,(
% 3.32/0.99    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f34])).
% 3.32/0.99  
% 3.32/0.99  fof(f82,plain,(
% 3.32/0.99    v1_funct_1(sK4)),
% 3.32/0.99    inference(cnf_transformation,[],[f50])).
% 3.32/0.99  
% 3.32/0.99  fof(f14,axiom,(
% 3.32/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 3.32/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f31,plain,(
% 3.32/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.32/0.99    inference(ennf_transformation,[],[f14])).
% 3.32/0.99  
% 3.32/0.99  fof(f32,plain,(
% 3.32/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.32/0.99    inference(flattening,[],[f31])).
% 3.32/0.99  
% 3.32/0.99  fof(f76,plain,(
% 3.32/0.99    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f32])).
% 3.32/0.99  
% 3.32/0.99  fof(f80,plain,(
% 3.32/0.99    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f36])).
% 3.32/0.99  
% 3.32/0.99  fof(f87,plain,(
% 3.32/0.99    ~m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK3,sK2) | ~v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))),
% 3.32/0.99    inference(cnf_transformation,[],[f50])).
% 3.32/0.99  
% 3.32/0.99  fof(f11,axiom,(
% 3.32/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.32/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f19,plain,(
% 3.32/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.32/0.99    inference(pure_predicate_removal,[],[f11])).
% 3.32/0.99  
% 3.32/0.99  fof(f27,plain,(
% 3.32/0.99    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.32/0.99    inference(ennf_transformation,[],[f19])).
% 3.32/0.99  
% 3.32/0.99  fof(f68,plain,(
% 3.32/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.32/0.99    inference(cnf_transformation,[],[f27])).
% 3.32/0.99  
% 3.32/0.99  fof(f7,axiom,(
% 3.32/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.32/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f22,plain,(
% 3.32/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.32/0.99    inference(ennf_transformation,[],[f7])).
% 3.32/0.99  
% 3.32/0.99  fof(f47,plain,(
% 3.32/0.99    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.32/0.99    inference(nnf_transformation,[],[f22])).
% 3.32/0.99  
% 3.32/0.99  fof(f63,plain,(
% 3.32/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f47])).
% 3.32/0.99  
% 3.32/0.99  fof(f77,plain,(
% 3.32/0.99    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f32])).
% 3.32/0.99  
% 3.32/0.99  fof(f86,plain,(
% 3.32/0.99    k1_xboole_0 = sK1 | k1_xboole_0 != sK2),
% 3.32/0.99    inference(cnf_transformation,[],[f50])).
% 3.32/0.99  
% 3.32/0.99  fof(f5,axiom,(
% 3.32/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.32/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f45,plain,(
% 3.32/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.32/0.99    inference(nnf_transformation,[],[f5])).
% 3.32/0.99  
% 3.32/0.99  fof(f46,plain,(
% 3.32/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.32/0.99    inference(flattening,[],[f45])).
% 3.32/0.99  
% 3.32/0.99  fof(f60,plain,(
% 3.32/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.32/0.99    inference(cnf_transformation,[],[f46])).
% 3.32/0.99  
% 3.32/0.99  fof(f91,plain,(
% 3.32/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.32/0.99    inference(equality_resolution,[],[f60])).
% 3.32/0.99  
% 3.32/0.99  fof(f73,plain,(
% 3.32/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.32/0.99    inference(cnf_transformation,[],[f48])).
% 3.32/0.99  
% 3.32/0.99  fof(f95,plain,(
% 3.32/0.99    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.32/0.99    inference(equality_resolution,[],[f73])).
% 3.32/0.99  
% 3.32/0.99  fof(f61,plain,(
% 3.32/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.32/0.99    inference(cnf_transformation,[],[f46])).
% 3.32/0.99  
% 3.32/0.99  fof(f90,plain,(
% 3.32/0.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.32/0.99    inference(equality_resolution,[],[f61])).
% 3.32/0.99  
% 3.32/0.99  fof(f4,axiom,(
% 3.32/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.32/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f58,plain,(
% 3.32/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f4])).
% 3.32/0.99  
% 3.32/0.99  fof(f3,axiom,(
% 3.32/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.32/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f43,plain,(
% 3.32/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.32/0.99    inference(nnf_transformation,[],[f3])).
% 3.32/0.99  
% 3.32/0.99  fof(f44,plain,(
% 3.32/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.32/0.99    inference(flattening,[],[f43])).
% 3.32/0.99  
% 3.32/0.99  fof(f57,plain,(
% 3.32/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f44])).
% 3.32/0.99  
% 3.32/0.99  cnf(c_33,negated_conjecture,
% 3.32/0.99      ( r1_tarski(sK3,sK1) ),
% 3.32/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1639,plain,
% 3.32/0.99      ( r1_tarski(sK3,sK1) = iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_24,plain,
% 3.32/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.32/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.32/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.32/0.99      | k1_xboole_0 = X2 ),
% 3.32/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_35,negated_conjecture,
% 3.32/0.99      ( v1_funct_2(sK4,sK1,sK2) ),
% 3.32/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_645,plain,
% 3.32/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.32/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.32/0.99      | sK4 != X0
% 3.32/0.99      | sK2 != X2
% 3.32/0.99      | sK1 != X1
% 3.32/0.99      | k1_xboole_0 = X2 ),
% 3.32/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_35]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_646,plain,
% 3.32/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.32/0.99      | k1_relset_1(sK1,sK2,sK4) = sK1
% 3.32/0.99      | k1_xboole_0 = sK2 ),
% 3.32/0.99      inference(unflattening,[status(thm)],[c_645]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_34,negated_conjecture,
% 3.32/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.32/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_648,plain,
% 3.32/0.99      ( k1_relset_1(sK1,sK2,sK4) = sK1 | k1_xboole_0 = sK2 ),
% 3.32/0.99      inference(global_propositional_subsumption,[status(thm)],[c_646,c_34]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1638,plain,
% 3.32/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_18,plain,
% 3.32/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.32/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.32/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1644,plain,
% 3.32/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.32/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2971,plain,
% 3.32/0.99      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_1638,c_1644]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_3023,plain,
% 3.32/0.99      ( k1_relat_1(sK4) = sK1 | sK2 = k1_xboole_0 ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_648,c_2971]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_15,plain,
% 3.32/0.99      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.32/0.99      | ~ v1_relat_1(X1)
% 3.32/0.99      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 3.32/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1646,plain,
% 3.32/0.99      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 3.32/0.99      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 3.32/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_3318,plain,
% 3.32/0.99      ( k1_relat_1(k7_relat_1(sK4,X0)) = X0
% 3.32/0.99      | sK2 = k1_xboole_0
% 3.32/0.99      | r1_tarski(X0,sK1) != iProver_top
% 3.32/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_3023,c_1646]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_39,plain,
% 3.32/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_16,plain,
% 3.32/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.32/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1917,plain,
% 3.32/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.32/0.99      | v1_relat_1(sK4) ),
% 3.32/0.99      inference(instantiation,[status(thm)],[c_16]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1918,plain,
% 3.32/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.32/0.99      | v1_relat_1(sK4) = iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_1917]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_3602,plain,
% 3.32/0.99      ( r1_tarski(X0,sK1) != iProver_top
% 3.32/0.99      | sK2 = k1_xboole_0
% 3.32/0.99      | k1_relat_1(k7_relat_1(sK4,X0)) = X0 ),
% 3.32/0.99      inference(global_propositional_subsumption,
% 3.32/0.99                [status(thm)],
% 3.32/0.99                [c_3318,c_39,c_1918]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_3603,plain,
% 3.32/0.99      ( k1_relat_1(k7_relat_1(sK4,X0)) = X0
% 3.32/0.99      | sK2 = k1_xboole_0
% 3.32/0.99      | r1_tarski(X0,sK1) != iProver_top ),
% 3.32/0.99      inference(renaming,[status(thm)],[c_3602]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_3614,plain,
% 3.32/0.99      ( k1_relat_1(k7_relat_1(sK4,sK3)) = sK3 | sK2 = k1_xboole_0 ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_1639,c_3603]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_28,plain,
% 3.32/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.32/0.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.32/0.99      | ~ v1_funct_1(X0)
% 3.32/0.99      | ~ v1_relat_1(X0) ),
% 3.32/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1640,plain,
% 3.32/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 3.32/0.99      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.32/0.99      | v1_funct_1(X0) != iProver_top
% 3.32/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_4151,plain,
% 3.32/0.99      ( sK2 = k1_xboole_0
% 3.32/0.99      | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
% 3.32/0.99      | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK3)),X0) != iProver_top
% 3.32/0.99      | v1_funct_1(k7_relat_1(sK4,sK3)) != iProver_top
% 3.32/0.99      | v1_relat_1(k7_relat_1(sK4,sK3)) != iProver_top ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_3614,c_1640]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_27,plain,
% 3.32/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.32/0.99      | ~ v1_funct_1(X0)
% 3.32/0.99      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 3.32/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1641,plain,
% 3.32/0.99      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 3.32/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.32/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_4350,plain,
% 3.32/0.99      ( k2_partfun1(sK1,sK2,sK4,X0) = k7_relat_1(sK4,X0)
% 3.32/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_1638,c_1641]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_36,negated_conjecture,
% 3.32/0.99      ( v1_funct_1(sK4) ),
% 3.32/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_37,plain,
% 3.32/0.99      ( v1_funct_1(sK4) = iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_4447,plain,
% 3.32/0.99      ( k2_partfun1(sK1,sK2,sK4,X0) = k7_relat_1(sK4,X0) ),
% 3.32/0.99      inference(global_propositional_subsumption,[status(thm)],[c_4350,c_37]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_26,plain,
% 3.32/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.32/0.99      | ~ v1_funct_1(X0)
% 3.32/0.99      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 3.32/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1642,plain,
% 3.32/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.32/0.99      | v1_funct_1(X0) != iProver_top
% 3.32/0.99      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_4233,plain,
% 3.32/0.99      ( v1_funct_1(k2_partfun1(sK1,sK2,sK4,X0)) = iProver_top
% 3.32/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_1638,c_1642]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1965,plain,
% 3.32/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.32/0.99      | v1_funct_1(k2_partfun1(X0,X1,sK4,X2))
% 3.32/0.99      | ~ v1_funct_1(sK4) ),
% 3.32/0.99      inference(instantiation,[status(thm)],[c_26]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2360,plain,
% 3.32/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.32/0.99      | v1_funct_1(k2_partfun1(sK1,sK2,sK4,X0))
% 3.32/0.99      | ~ v1_funct_1(sK4) ),
% 3.32/0.99      inference(instantiation,[status(thm)],[c_1965]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2361,plain,
% 3.32/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.32/0.99      | v1_funct_1(k2_partfun1(sK1,sK2,sK4,X0)) = iProver_top
% 3.32/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_2360]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_4388,plain,
% 3.32/0.99      ( v1_funct_1(k2_partfun1(sK1,sK2,sK4,X0)) = iProver_top ),
% 3.32/0.99      inference(global_propositional_subsumption,
% 3.32/0.99                [status(thm)],
% 3.32/0.99                [c_4233,c_37,c_39,c_2361]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_4456,plain,
% 3.32/0.99      ( v1_funct_1(k7_relat_1(sK4,X0)) = iProver_top ),
% 3.32/0.99      inference(demodulation,[status(thm)],[c_4447,c_4388]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_4724,plain,
% 3.32/0.99      ( sK2 = k1_xboole_0
% 3.32/0.99      | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
% 3.32/0.99      | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK3)),X0) != iProver_top
% 3.32/0.99      | v1_relat_1(k7_relat_1(sK4,sK3)) != iProver_top ),
% 3.32/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_4151,c_4456]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_29,plain,
% 3.32/0.99      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.32/0.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.32/0.99      | ~ v1_funct_1(X0)
% 3.32/0.99      | ~ v1_relat_1(X0) ),
% 3.32/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_31,negated_conjecture,
% 3.32/0.99      ( ~ v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK3,sK2)
% 3.32/0.99      | ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.32/0.99      | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3)) ),
% 3.32/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_656,plain,
% 3.32/0.99      ( ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.32/0.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.32/0.99      | ~ v1_funct_1(X0)
% 3.32/0.99      | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))
% 3.32/0.99      | ~ v1_relat_1(X0)
% 3.32/0.99      | k2_partfun1(sK1,sK2,sK4,sK3) != X0
% 3.32/0.99      | k1_relat_1(X0) != sK3
% 3.32/0.99      | sK2 != X1 ),
% 3.32/0.99      inference(resolution_lifted,[status(thm)],[c_29,c_31]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_657,plain,
% 3.32/0.99      ( ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.32/0.99      | ~ r1_tarski(k2_relat_1(k2_partfun1(sK1,sK2,sK4,sK3)),sK2)
% 3.32/0.99      | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))
% 3.32/0.99      | ~ v1_relat_1(k2_partfun1(sK1,sK2,sK4,sK3))
% 3.32/0.99      | k1_relat_1(k2_partfun1(sK1,sK2,sK4,sK3)) != sK3 ),
% 3.32/0.99      inference(unflattening,[status(thm)],[c_656]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_17,plain,
% 3.32/0.99      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.32/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_13,plain,
% 3.32/0.99      ( ~ v5_relat_1(X0,X1) | r1_tarski(k2_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 3.32/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_371,plain,
% 3.32/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.32/0.99      | r1_tarski(k2_relat_1(X0),X2)
% 3.32/0.99      | ~ v1_relat_1(X0) ),
% 3.32/0.99      inference(resolution,[status(thm)],[c_17,c_13]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_375,plain,
% 3.32/0.99      ( r1_tarski(k2_relat_1(X0),X2)
% 3.32/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.32/0.99      inference(global_propositional_subsumption,[status(thm)],[c_371,c_16]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_376,plain,
% 3.32/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.32/0.99      | r1_tarski(k2_relat_1(X0),X2) ),
% 3.32/0.99      inference(renaming,[status(thm)],[c_375]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_669,plain,
% 3.32/0.99      ( ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.32/0.99      | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))
% 3.32/0.99      | k1_relat_1(k2_partfun1(sK1,sK2,sK4,sK3)) != sK3 ),
% 3.32/0.99      inference(forward_subsumption_resolution,
% 3.32/0.99                [status(thm)],
% 3.32/0.99                [c_657,c_16,c_376]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1626,plain,
% 3.32/0.99      ( k1_relat_1(k2_partfun1(sK1,sK2,sK4,sK3)) != sK3
% 3.32/0.99      | m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.32/0.99      | v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3)) != iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_669]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_4454,plain,
% 3.32/0.99      ( k1_relat_1(k7_relat_1(sK4,sK3)) != sK3
% 3.32/0.99      | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.32/0.99      | v1_funct_1(k7_relat_1(sK4,sK3)) != iProver_top ),
% 3.32/0.99      inference(demodulation,[status(thm)],[c_4447,c_1626]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_4470,plain,
% 3.32/0.99      ( k1_relat_1(k7_relat_1(sK4,sK3)) != sK3
% 3.32/0.99      | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 3.32/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_4454,c_4456]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_4880,plain,
% 3.32/0.99      ( sK2 = k1_xboole_0
% 3.32/0.99      | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_3614,c_4470]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_5399,plain,
% 3.32/0.99      ( sK2 = k1_xboole_0
% 3.32/0.99      | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK3)),sK2) != iProver_top
% 3.32/0.99      | v1_relat_1(k7_relat_1(sK4,sK3)) != iProver_top ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_4724,c_4880]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_25,plain,
% 3.32/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.32/0.99      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.32/0.99      | ~ v1_funct_1(X0) ),
% 3.32/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1643,plain,
% 3.32/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.32/0.99      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.32/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_4886,plain,
% 3.32/0.99      ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top
% 3.32/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.32/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_4447,c_1643]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_5402,plain,
% 3.32/0.99      ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.32/0.99      inference(global_propositional_subsumption,
% 3.32/0.99                [status(thm)],
% 3.32/0.99                [c_4886,c_37,c_39]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1645,plain,
% 3.32/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.32/0.99      | v1_relat_1(X0) = iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_5411,plain,
% 3.32/0.99      ( v1_relat_1(k7_relat_1(sK4,X0)) = iProver_top ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_5402,c_1645]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1635,plain,
% 3.32/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.32/0.99      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_376]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_5410,plain,
% 3.32/0.99      ( r1_tarski(k2_relat_1(k7_relat_1(sK4,X0)),sK2) = iProver_top ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_5402,c_1635]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_5917,plain,
% 3.32/0.99      ( sK2 = k1_xboole_0 ),
% 3.32/0.99      inference(forward_subsumption_resolution,
% 3.32/0.99                [status(thm)],
% 3.32/0.99                [c_5399,c_5411,c_5410]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_5413,plain,
% 3.32/0.99      ( k1_relset_1(sK1,sK2,k7_relat_1(sK4,X0)) = k1_relat_1(k7_relat_1(sK4,X0)) ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_5402,c_1644]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_5919,plain,
% 3.32/0.99      ( k1_relset_1(sK1,k1_xboole_0,k7_relat_1(sK4,X0)) = k1_relat_1(k7_relat_1(sK4,X0)) ),
% 3.32/0.99      inference(demodulation,[status(thm)],[c_5917,c_5413]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_32,negated_conjecture,
% 3.32/0.99      ( k1_xboole_0 != sK2 | k1_xboole_0 = sK1 ),
% 3.32/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_5936,plain,
% 3.32/0.99      ( sK1 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.32/0.99      inference(demodulation,[status(thm)],[c_5917,c_32]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_5937,plain,
% 3.32/0.99      ( sK1 = k1_xboole_0 ),
% 3.32/0.99      inference(equality_resolution_simp,[status(thm)],[c_5936]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_6009,plain,
% 3.32/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK4,X0)) = k1_relat_1(k7_relat_1(sK4,X0)) ),
% 3.32/0.99      inference(light_normalisation,[status(thm)],[c_5919,c_5937]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_5921,plain,
% 3.32/0.99      ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
% 3.32/0.99      inference(demodulation,[status(thm)],[c_5917,c_5402]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_5988,plain,
% 3.32/0.99      ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.32/0.99      inference(light_normalisation,[status(thm)],[c_5921,c_5937]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_9,plain,
% 3.32/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.32/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_5990,plain,
% 3.32/0.99      ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.32/0.99      inference(demodulation,[status(thm)],[c_5988,c_9]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_21,plain,
% 3.32/0.99      ( v1_funct_2(X0,k1_xboole_0,X1)
% 3.32/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.32/0.99      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 3.32/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_570,plain,
% 3.32/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.32/0.99      | ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.32/0.99      | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))
% 3.32/0.99      | k2_partfun1(sK1,sK2,sK4,sK3) != X0
% 3.32/0.99      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 3.32/0.99      | sK3 != k1_xboole_0
% 3.32/0.99      | sK2 != X1 ),
% 3.32/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_31]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_571,plain,
% 3.32/0.99      ( ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.32/0.99      | ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
% 3.32/0.99      | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))
% 3.32/0.99      | k1_relset_1(k1_xboole_0,sK2,k2_partfun1(sK1,sK2,sK4,sK3)) != k1_xboole_0
% 3.32/0.99      | sK3 != k1_xboole_0 ),
% 3.32/0.99      inference(unflattening,[status(thm)],[c_570]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1630,plain,
% 3.32/0.99      ( k1_relset_1(k1_xboole_0,sK2,k2_partfun1(sK1,sK2,sK4,sK3)) != k1_xboole_0
% 3.32/0.99      | sK3 != k1_xboole_0
% 3.32/0.99      | m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.32/0.99      | m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top
% 3.32/0.99      | v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3)) != iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_571]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1834,plain,
% 3.32/0.99      ( k1_relset_1(k1_xboole_0,sK2,k2_partfun1(sK1,sK2,sK4,sK3)) != k1_xboole_0
% 3.32/0.99      | sK3 != k1_xboole_0
% 3.32/0.99      | m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.32/0.99      | m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.32/0.99      | v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3)) != iProver_top ),
% 3.32/0.99      inference(demodulation,[status(thm)],[c_1630,c_9]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2094,plain,
% 3.32/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.32/0.99      | v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))
% 3.32/0.99      | ~ v1_funct_1(sK4) ),
% 3.32/0.99      inference(instantiation,[status(thm)],[c_1965]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2095,plain,
% 3.32/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.32/0.99      | v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3)) = iProver_top
% 3.32/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_2094]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2366,plain,
% 3.32/0.99      ( m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.32/0.99      | m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.32/0.99      | sK3 != k1_xboole_0
% 3.32/0.99      | k1_relset_1(k1_xboole_0,sK2,k2_partfun1(sK1,sK2,sK4,sK3)) != k1_xboole_0 ),
% 3.32/0.99      inference(global_propositional_subsumption,
% 3.32/0.99                [status(thm)],
% 3.32/0.99                [c_1834,c_37,c_39,c_2095]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2367,plain,
% 3.32/0.99      ( k1_relset_1(k1_xboole_0,sK2,k2_partfun1(sK1,sK2,sK4,sK3)) != k1_xboole_0
% 3.32/0.99      | sK3 != k1_xboole_0
% 3.32/0.99      | m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.32/0.99      | m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.32/0.99      inference(renaming,[status(thm)],[c_2366]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_4451,plain,
% 3.32/0.99      ( k1_relset_1(k1_xboole_0,sK2,k7_relat_1(sK4,sK3)) != k1_xboole_0
% 3.32/0.99      | sK3 != k1_xboole_0
% 3.32/0.99      | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.32/0.99      | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.32/0.99      inference(demodulation,[status(thm)],[c_4447,c_2367]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_5923,plain,
% 3.32/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK4,sK3)) != k1_xboole_0
% 3.32/0.99      | sK3 != k1_xboole_0
% 3.32/0.99      | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) != iProver_top
% 3.32/0.99      | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.32/0.99      inference(demodulation,[status(thm)],[c_5917,c_4451]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_8,plain,
% 3.32/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.32/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_5979,plain,
% 3.32/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK4,sK3)) != k1_xboole_0
% 3.32/0.99      | sK3 != k1_xboole_0
% 3.32/0.99      | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.32/0.99      inference(demodulation,[status(thm)],[c_5923,c_8]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_5992,plain,
% 3.32/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK4,sK3)) != k1_xboole_0
% 3.32/0.99      | sK3 != k1_xboole_0 ),
% 3.32/0.99      inference(backward_subsumption_resolution,[status(thm)],[c_5990,c_5979]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_6011,plain,
% 3.32/0.99      ( k1_relat_1(k7_relat_1(sK4,sK3)) != k1_xboole_0 | sK3 != k1_xboole_0 ),
% 3.32/0.99      inference(demodulation,[status(thm)],[c_6009,c_5992]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_7,plain,
% 3.32/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 3.32/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2961,plain,
% 3.32/0.99      ( r1_tarski(k1_xboole_0,sK3) ),
% 3.32/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2962,plain,
% 3.32/0.99      ( r1_tarski(k1_xboole_0,sK3) = iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_2961]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_4,plain,
% 3.32/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.32/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1650,plain,
% 3.32/0.99      ( X0 = X1
% 3.32/0.99      | r1_tarski(X1,X0) != iProver_top
% 3.32/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_3125,plain,
% 3.32/0.99      ( sK3 = sK1 | r1_tarski(sK1,sK3) != iProver_top ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_1639,c_1650]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_6037,plain,
% 3.32/0.99      ( sK3 = k1_xboole_0 | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 3.32/0.99      inference(demodulation,[status(thm)],[c_5937,c_3125]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_7348,plain,
% 3.32/0.99      ( k1_relat_1(k7_relat_1(sK4,sK3)) != k1_xboole_0 ),
% 3.32/0.99      inference(global_propositional_subsumption,
% 3.32/0.99                [status(thm)],
% 3.32/0.99                [c_6011,c_2962,c_6037]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1648,plain,
% 3.32/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_3612,plain,
% 3.32/0.99      ( k1_relat_1(k7_relat_1(sK4,k1_xboole_0)) = k1_xboole_0
% 3.32/0.99      | sK2 = k1_xboole_0 ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_1648,c_3603]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1993,plain,
% 3.32/0.99      ( ~ r1_tarski(X0,k1_relat_1(sK4))
% 3.32/0.99      | ~ v1_relat_1(sK4)
% 3.32/0.99      | k1_relat_1(k7_relat_1(sK4,X0)) = X0 ),
% 3.32/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1995,plain,
% 3.32/0.99      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK4))
% 3.32/0.99      | ~ v1_relat_1(sK4)
% 3.32/0.99      | k1_relat_1(k7_relat_1(sK4,k1_xboole_0)) = k1_xboole_0 ),
% 3.32/0.99      inference(instantiation,[status(thm)],[c_1993]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2313,plain,
% 3.32/0.99      ( r1_tarski(k1_xboole_0,k1_relat_1(sK4)) ),
% 3.32/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_4027,plain,
% 3.32/0.99      ( k1_relat_1(k7_relat_1(sK4,k1_xboole_0)) = k1_xboole_0 ),
% 3.32/0.99      inference(global_propositional_subsumption,
% 3.32/0.99                [status(thm)],
% 3.32/0.99                [c_3612,c_34,c_1917,c_1995,c_2313]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_7138,plain,
% 3.32/0.99      ( sK3 = k1_xboole_0 ),
% 3.32/0.99      inference(global_propositional_subsumption,[status(thm)],[c_6037,c_2962]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_7350,plain,
% 3.32/0.99      ( k1_xboole_0 != k1_xboole_0 ),
% 3.32/0.99      inference(light_normalisation,[status(thm)],[c_7348,c_4027,c_7138]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_7351,plain,
% 3.32/0.99      ( $false ),
% 3.32/0.99      inference(equality_resolution_simp,[status(thm)],[c_7350]) ).
% 3.32/0.99  
% 3.32/0.99  
% 3.32/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.32/0.99  
% 3.32/0.99  ------                               Statistics
% 3.32/0.99  
% 3.32/0.99  ------ General
% 3.32/0.99  
% 3.32/0.99  abstr_ref_over_cycles:                  0
% 3.32/0.99  abstr_ref_under_cycles:                 0
% 3.32/0.99  gc_basic_clause_elim:                   0
% 3.32/0.99  forced_gc_time:                         0
% 3.32/0.99  parsing_time:                           0.01
% 3.32/0.99  unif_index_cands_time:                  0.
% 3.32/0.99  unif_index_add_time:                    0.
% 3.32/0.99  orderings_time:                         0.
% 3.32/0.99  out_proof_time:                         0.01
% 3.32/0.99  total_time:                             0.297
% 3.32/0.99  num_of_symbols:                         52
% 3.32/0.99  num_of_terms:                           7127
% 3.32/0.99  
% 3.32/0.99  ------ Preprocessing
% 3.32/0.99  
% 3.32/0.99  num_of_splits:                          0
% 3.32/0.99  num_of_split_atoms:                     0
% 3.32/0.99  num_of_reused_defs:                     0
% 3.32/0.99  num_eq_ax_congr_red:                    25
% 3.32/0.99  num_of_sem_filtered_clauses:            1
% 3.32/0.99  num_of_subtypes:                        0
% 3.32/0.99  monotx_restored_types:                  0
% 3.32/0.99  sat_num_of_epr_types:                   0
% 3.32/0.99  sat_num_of_non_cyclic_types:            0
% 3.32/0.99  sat_guarded_non_collapsed_types:        0
% 3.32/0.99  num_pure_diseq_elim:                    0
% 3.32/0.99  simp_replaced_by:                       0
% 3.32/0.99  res_preprocessed:                       160
% 3.32/0.99  prep_upred:                             0
% 3.32/0.99  prep_unflattend:                        47
% 3.32/0.99  smt_new_axioms:                         0
% 3.32/0.99  pred_elim_cands:                        5
% 3.32/0.99  pred_elim:                              3
% 3.32/0.99  pred_elim_cl:                           1
% 3.32/0.99  pred_elim_cycles:                       6
% 3.32/0.99  merged_defs:                            0
% 3.32/0.99  merged_defs_ncl:                        0
% 3.32/0.99  bin_hyper_res:                          0
% 3.32/0.99  prep_cycles:                            4
% 3.32/0.99  pred_elim_time:                         0.014
% 3.32/0.99  splitting_time:                         0.
% 3.32/0.99  sem_filter_time:                        0.
% 3.32/0.99  monotx_time:                            0.001
% 3.32/0.99  subtype_inf_time:                       0.
% 3.32/0.99  
% 3.32/0.99  ------ Problem properties
% 3.32/0.99  
% 3.32/0.99  clauses:                                34
% 3.32/0.99  conjectures:                            4
% 3.32/0.99  epr:                                    7
% 3.32/0.99  horn:                                   28
% 3.32/0.99  ground:                                 12
% 3.32/0.99  unary:                                  7
% 3.32/0.99  binary:                                 9
% 3.32/0.99  lits:                                   93
% 3.32/0.99  lits_eq:                                34
% 3.32/0.99  fd_pure:                                0
% 3.32/0.99  fd_pseudo:                              0
% 3.32/0.99  fd_cond:                                3
% 3.32/0.99  fd_pseudo_cond:                         1
% 3.32/0.99  ac_symbols:                             0
% 3.32/0.99  
% 3.32/0.99  ------ Propositional Solver
% 3.32/0.99  
% 3.32/0.99  prop_solver_calls:                      27
% 3.32/0.99  prop_fast_solver_calls:                 1239
% 3.32/0.99  smt_solver_calls:                       0
% 3.32/0.99  smt_fast_solver_calls:                  0
% 3.32/0.99  prop_num_of_clauses:                    2694
% 3.32/0.99  prop_preprocess_simplified:             8520
% 3.32/0.99  prop_fo_subsumed:                       23
% 3.32/0.99  prop_solver_time:                       0.
% 3.32/0.99  smt_solver_time:                        0.
% 3.32/0.99  smt_fast_solver_time:                   0.
% 3.32/0.99  prop_fast_solver_time:                  0.
% 3.32/0.99  prop_unsat_core_time:                   0.
% 3.32/0.99  
% 3.32/0.99  ------ QBF
% 3.32/0.99  
% 3.32/0.99  qbf_q_res:                              0
% 3.32/0.99  qbf_num_tautologies:                    0
% 3.32/0.99  qbf_prep_cycles:                        0
% 3.32/0.99  
% 3.32/0.99  ------ BMC1
% 3.32/0.99  
% 3.32/0.99  bmc1_current_bound:                     -1
% 3.32/0.99  bmc1_last_solved_bound:                 -1
% 3.32/0.99  bmc1_unsat_core_size:                   -1
% 3.32/0.99  bmc1_unsat_core_parents_size:           -1
% 3.32/0.99  bmc1_merge_next_fun:                    0
% 3.32/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.32/0.99  
% 3.32/0.99  ------ Instantiation
% 3.32/0.99  
% 3.32/0.99  inst_num_of_clauses:                    780
% 3.32/0.99  inst_num_in_passive:                    435
% 3.32/0.99  inst_num_in_active:                     325
% 3.32/0.99  inst_num_in_unprocessed:                20
% 3.32/0.99  inst_num_of_loops:                      440
% 3.32/0.99  inst_num_of_learning_restarts:          0
% 3.32/0.99  inst_num_moves_active_passive:          113
% 3.32/0.99  inst_lit_activity:                      0
% 3.32/0.99  inst_lit_activity_moves:                0
% 3.32/0.99  inst_num_tautologies:                   0
% 3.32/0.99  inst_num_prop_implied:                  0
% 3.32/0.99  inst_num_existing_simplified:           0
% 3.32/0.99  inst_num_eq_res_simplified:             0
% 3.32/0.99  inst_num_child_elim:                    0
% 3.32/0.99  inst_num_of_dismatching_blockings:      297
% 3.32/0.99  inst_num_of_non_proper_insts:           582
% 3.32/0.99  inst_num_of_duplicates:                 0
% 3.32/0.99  inst_inst_num_from_inst_to_res:         0
% 3.32/0.99  inst_dismatching_checking_time:         0.
% 3.32/0.99  
% 3.32/0.99  ------ Resolution
% 3.32/0.99  
% 3.32/0.99  res_num_of_clauses:                     0
% 3.32/0.99  res_num_in_passive:                     0
% 3.32/0.99  res_num_in_active:                      0
% 3.32/0.99  res_num_of_loops:                       164
% 3.32/0.99  res_forward_subset_subsumed:            30
% 3.32/0.99  res_backward_subset_subsumed:           0
% 3.32/0.99  res_forward_subsumed:                   0
% 3.32/0.99  res_backward_subsumed:                  0
% 3.32/0.99  res_forward_subsumption_resolution:     5
% 3.32/0.99  res_backward_subsumption_resolution:    0
% 3.32/0.99  res_clause_to_clause_subsumption:       381
% 3.32/0.99  res_orphan_elimination:                 0
% 3.32/0.99  res_tautology_del:                      41
% 3.32/0.99  res_num_eq_res_simplified:              1
% 3.32/0.99  res_num_sel_changes:                    0
% 3.32/0.99  res_moves_from_active_to_pass:          0
% 3.32/0.99  
% 3.32/0.99  ------ Superposition
% 3.32/0.99  
% 3.32/0.99  sup_time_total:                         0.
% 3.32/0.99  sup_time_generating:                    0.
% 3.32/0.99  sup_time_sim_full:                      0.
% 3.32/0.99  sup_time_sim_immed:                     0.
% 3.32/0.99  
% 3.32/0.99  sup_num_of_clauses:                     114
% 3.32/0.99  sup_num_in_active:                      50
% 3.32/0.99  sup_num_in_passive:                     64
% 3.32/0.99  sup_num_of_loops:                       87
% 3.32/0.99  sup_fw_superposition:                   55
% 3.32/0.99  sup_bw_superposition:                   76
% 3.32/0.99  sup_immediate_simplified:               40
% 3.32/0.99  sup_given_eliminated:                   0
% 3.32/0.99  comparisons_done:                       0
% 3.32/0.99  comparisons_avoided:                    22
% 3.32/0.99  
% 3.32/0.99  ------ Simplifications
% 3.32/0.99  
% 3.32/0.99  
% 3.32/0.99  sim_fw_subset_subsumed:                 12
% 3.32/0.99  sim_bw_subset_subsumed:                 9
% 3.32/0.99  sim_fw_subsumed:                        5
% 3.32/0.99  sim_bw_subsumed:                        0
% 3.32/0.99  sim_fw_subsumption_res:                 8
% 3.32/0.99  sim_bw_subsumption_res:                 3
% 3.32/0.99  sim_tautology_del:                      5
% 3.32/0.99  sim_eq_tautology_del:                   6
% 3.32/0.99  sim_eq_res_simp:                        3
% 3.32/0.99  sim_fw_demodulated:                     12
% 3.32/0.99  sim_bw_demodulated:                     34
% 3.32/0.99  sim_light_normalised:                   13
% 3.32/0.99  sim_joinable_taut:                      0
% 3.32/0.99  sim_joinable_simp:                      0
% 3.32/0.99  sim_ac_normalised:                      0
% 3.32/0.99  sim_smt_subsumption:                    0
% 3.32/0.99  
%------------------------------------------------------------------------------
