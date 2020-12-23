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
% DateTime   : Thu Dec  3 12:02:17 EST 2020

% Result     : Theorem 3.94s
% Output     : CNFRefutation 3.94s
% Verified   : 
% Statistics : Number of formulae       :  211 (1194 expanded)
%              Number of clauses        :  121 ( 351 expanded)
%              Number of leaves         :   24 ( 304 expanded)
%              Depth                    :   19
%              Number of atoms          :  660 (7572 expanded)
%              Number of equality atoms :  247 ( 624 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
           => ( v2_funct_2(X3,X0)
              & v2_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
             => ( v2_funct_2(X3,X0)
                & v2_funct_1(X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f40,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f41,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
     => ( ( ~ v2_funct_2(sK3,X0)
          | ~ v2_funct_1(X2) )
        & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0))
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(sK3,X1,X0)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( ~ v2_funct_2(X3,X0)
              | ~ v2_funct_1(X2) )
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v2_funct_2(X3,sK0)
            | ~ v2_funct_1(sK2) )
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ( ~ v2_funct_2(sK3,sK0)
      | ~ v2_funct_1(sK2) )
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f41,f49,f48])).

fof(f84,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f50])).

fof(f87,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f50])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f36])).

fof(f78,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f85,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f82,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
           => ( v2_funct_1(X3)
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f38])).

fof(f80,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_funct_1(X3)
      | k1_xboole_0 = X2
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f83,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f86,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f11,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f18,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f94,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f67,f79])).

fof(f68,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f93,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f68,f79])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f90,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f65,f79])).

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

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f97,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f51])).

fof(f53,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f99,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f75])).

fof(f89,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f96,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k2_relat_1(X0) = k1_xboole_0
          | k1_relat_1(X0) = k1_xboole_0 )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k2_relat_1(X0) != k1_xboole_0
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k2_relat_1(X0) != k1_xboole_0
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f62,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_relat_1(X0) != k1_xboole_0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f63,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k2_relat_1(X0) != k1_xboole_0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f30])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f88,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f50])).

fof(f14,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f95,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f73,f79])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f34])).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f64,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f91,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f64,f79])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1156,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1159,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1162,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3842,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1159,c_1162])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_41,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_4157,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3842,c_41])).

cnf(c_4158,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4157])).

cnf(c_4169,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1156,c_4158])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1496,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X1,X2,X3,X4,X0,sK3) = k5_relat_1(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_1794,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X0,X1,X2,X3,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1496])).

cnf(c_2269,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(sK0,sK1,X0,X1,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1794])).

cnf(c_3485,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2269])).

cnf(c_4294,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4169,c_37,c_35,c_34,c_32,c_3485])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v2_funct_1(X3)
    | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1160,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_funct_2(X3,X4,X2) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v2_funct_1(X3) = iProver_top
    | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4301,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4294,c_1160])).

cnf(c_38,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_36,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_39,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_40,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_42,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_43,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_17,plain,
    ( v1_relat_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_83,plain,
    ( v1_relat_1(k6_partfun1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_16,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_85,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_87,plain,
    ( v2_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_85])).

cnf(c_13,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_89,plain,
    ( k2_relat_1(k6_partfun1(k1_xboole_0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_119,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_123,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_6,plain,
    ( v5_relat_1(X0,X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_23,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_30,negated_conjecture,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_427,plain,
    ( ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != sK0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_30])).

cnf(c_428,plain,
    ( ~ v5_relat_1(sK3,k2_relat_1(sK3))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != sK0 ),
    inference(unflattening,[status(thm)],[c_427])).

cnf(c_481,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != X1
    | k2_relat_1(sK3) != sK0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_428])).

cnf(c_482,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(sK3))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != sK0 ),
    inference(unflattening,[status(thm)],[c_481])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_492,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != sK0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_482,c_1])).

cnf(c_493,plain,
    ( k2_relat_1(sK3) != sK0
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_492])).

cnf(c_688,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1398,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(k6_partfun1(X1))
    | X0 != k6_partfun1(X1) ),
    inference(instantiation,[status(thm)],[c_688])).

cnf(c_1399,plain,
    ( X0 != k6_partfun1(X1)
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k6_partfun1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1398])).

cnf(c_1401,plain,
    ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
    | v2_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
    | v2_funct_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1399])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1575,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_678,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1647,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_678])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1747,plain,
    ( ~ v1_relat_1(k6_partfun1(X0))
    | k2_relat_1(k6_partfun1(X0)) != k1_xboole_0
    | k1_xboole_0 = k6_partfun1(X0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1751,plain,
    ( ~ v1_relat_1(k6_partfun1(k1_xboole_0))
    | k2_relat_1(k6_partfun1(k1_xboole_0)) != k1_xboole_0
    | k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1747])).

cnf(c_679,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2600,plain,
    ( X0 != X1
    | X0 = sK0
    | sK0 != X1 ),
    inference(instantiation,[status(thm)],[c_679])).

cnf(c_2601,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2600])).

cnf(c_18,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_7,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_448,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_18,c_7])).

cnf(c_1151,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_448])).

cnf(c_2521,plain,
    ( r1_tarski(k2_relat_1(sK3),sK0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1159,c_1151])).

cnf(c_1175,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2741,plain,
    ( k2_relat_1(sK3) = sK0
    | r1_tarski(sK0,k2_relat_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2521,c_1175])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1173,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2973,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1159,c_1173])).

cnf(c_8,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1172,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2989,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2973,c_1172])).

cnf(c_3021,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(sK2)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_688])).

cnf(c_3022,plain,
    ( sK2 != X0
    | v2_funct_1(X0) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3021])).

cnf(c_3024,plain,
    ( sK2 != k1_xboole_0
    | v2_funct_1(sK2) = iProver_top
    | v2_funct_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3022])).

cnf(c_2974,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1156,c_1173])).

cnf(c_3146,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2974,c_1172])).

cnf(c_3147,plain,
    ( v1_relat_1(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3146])).

cnf(c_19,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_5,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_388,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_19,c_5])).

cnf(c_1153,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_388])).

cnf(c_3154,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1156,c_1153])).

cnf(c_2715,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | r1_tarski(k1_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_388])).

cnf(c_2716,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | r1_tarski(k1_relat_1(sK2),sK0) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2715])).

cnf(c_3544,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3154,c_40,c_2716,c_3146])).

cnf(c_3549,plain,
    ( k1_relat_1(sK2) = sK0
    | r1_tarski(sK0,k1_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3544,c_1175])).

cnf(c_2560,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_679])).

cnf(c_4775,plain,
    ( X0 != sK2
    | sK2 = X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2560])).

cnf(c_4776,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_4775])).

cnf(c_21,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_31,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_409,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_31])).

cnf(c_410,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_409])).

cnf(c_22,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_418,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_410,c_22])).

cnf(c_1152,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_418])).

cnf(c_4297,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4294,c_1152])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1164,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4299,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4294,c_1164])).

cnf(c_4966,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4297,c_38,c_40,c_41,c_43,c_4299])).

cnf(c_10,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1170,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4971,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4966,c_1170])).

cnf(c_4975,plain,
    ( r1_tarski(sK0,k2_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4971,c_13])).

cnf(c_9,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1171,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4970,plain,
    ( r1_tarski(k1_relat_1(k6_partfun1(sK0)),k1_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4966,c_1171])).

cnf(c_14,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_4982,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4970,c_14])).

cnf(c_3685,plain,
    ( k1_relat_1(sK2) != X0
    | k1_relat_1(sK2) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_679])).

cnf(c_14547,plain,
    ( k1_relat_1(sK2) != sK0
    | k1_relat_1(sK2) = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_3685])).

cnf(c_16315,plain,
    ( v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4301,c_38,c_39,c_40,c_41,c_42,c_43,c_83,c_87,c_89,c_119,c_123,c_493,c_1401,c_1575,c_1647,c_1751,c_2601,c_2741,c_2989,c_3024,c_3146,c_3147,c_3549,c_4776,c_4975,c_4982,c_14547])).

cnf(c_16319,plain,
    ( v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_16315,c_4966])).

cnf(c_1167,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_16321,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_16319,c_1167])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n019.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:20:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.94/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.94/0.98  
% 3.94/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.94/0.98  
% 3.94/0.98  ------  iProver source info
% 3.94/0.98  
% 3.94/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.94/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.94/0.98  git: non_committed_changes: false
% 3.94/0.98  git: last_make_outside_of_git: false
% 3.94/0.98  
% 3.94/0.98  ------ 
% 3.94/0.98  
% 3.94/0.98  ------ Input Options
% 3.94/0.98  
% 3.94/0.98  --out_options                           all
% 3.94/0.98  --tptp_safe_out                         true
% 3.94/0.98  --problem_path                          ""
% 3.94/0.98  --include_path                          ""
% 3.94/0.98  --clausifier                            res/vclausify_rel
% 3.94/0.98  --clausifier_options                    --mode clausify
% 3.94/0.98  --stdin                                 false
% 3.94/0.98  --stats_out                             all
% 3.94/0.98  
% 3.94/0.98  ------ General Options
% 3.94/0.98  
% 3.94/0.98  --fof                                   false
% 3.94/0.98  --time_out_real                         305.
% 3.94/0.98  --time_out_virtual                      -1.
% 3.94/0.98  --symbol_type_check                     false
% 3.94/0.98  --clausify_out                          false
% 3.94/0.98  --sig_cnt_out                           false
% 3.94/0.98  --trig_cnt_out                          false
% 3.94/0.98  --trig_cnt_out_tolerance                1.
% 3.94/0.98  --trig_cnt_out_sk_spl                   false
% 3.94/0.98  --abstr_cl_out                          false
% 3.94/0.98  
% 3.94/0.98  ------ Global Options
% 3.94/0.98  
% 3.94/0.98  --schedule                              default
% 3.94/0.98  --add_important_lit                     false
% 3.94/0.98  --prop_solver_per_cl                    1000
% 3.94/0.98  --min_unsat_core                        false
% 3.94/0.98  --soft_assumptions                      false
% 3.94/0.98  --soft_lemma_size                       3
% 3.94/0.98  --prop_impl_unit_size                   0
% 3.94/0.98  --prop_impl_unit                        []
% 3.94/0.98  --share_sel_clauses                     true
% 3.94/0.98  --reset_solvers                         false
% 3.94/0.98  --bc_imp_inh                            [conj_cone]
% 3.94/0.98  --conj_cone_tolerance                   3.
% 3.94/0.98  --extra_neg_conj                        none
% 3.94/0.98  --large_theory_mode                     true
% 3.94/0.98  --prolific_symb_bound                   200
% 3.94/0.98  --lt_threshold                          2000
% 3.94/0.98  --clause_weak_htbl                      true
% 3.94/0.98  --gc_record_bc_elim                     false
% 3.94/0.98  
% 3.94/0.98  ------ Preprocessing Options
% 3.94/0.98  
% 3.94/0.98  --preprocessing_flag                    true
% 3.94/0.98  --time_out_prep_mult                    0.1
% 3.94/0.98  --splitting_mode                        input
% 3.94/0.98  --splitting_grd                         true
% 3.94/0.98  --splitting_cvd                         false
% 3.94/0.98  --splitting_cvd_svl                     false
% 3.94/0.98  --splitting_nvd                         32
% 3.94/0.98  --sub_typing                            true
% 3.94/0.98  --prep_gs_sim                           true
% 3.94/0.98  --prep_unflatten                        true
% 3.94/0.98  --prep_res_sim                          true
% 3.94/0.98  --prep_upred                            true
% 3.94/0.98  --prep_sem_filter                       exhaustive
% 3.94/0.98  --prep_sem_filter_out                   false
% 3.94/0.98  --pred_elim                             true
% 3.94/0.98  --res_sim_input                         true
% 3.94/0.98  --eq_ax_congr_red                       true
% 3.94/0.98  --pure_diseq_elim                       true
% 3.94/0.98  --brand_transform                       false
% 3.94/0.98  --non_eq_to_eq                          false
% 3.94/0.98  --prep_def_merge                        true
% 3.94/0.98  --prep_def_merge_prop_impl              false
% 3.94/0.98  --prep_def_merge_mbd                    true
% 3.94/0.98  --prep_def_merge_tr_red                 false
% 3.94/0.98  --prep_def_merge_tr_cl                  false
% 3.94/0.98  --smt_preprocessing                     true
% 3.94/0.98  --smt_ac_axioms                         fast
% 3.94/0.98  --preprocessed_out                      false
% 3.94/0.98  --preprocessed_stats                    false
% 3.94/0.98  
% 3.94/0.98  ------ Abstraction refinement Options
% 3.94/0.98  
% 3.94/0.98  --abstr_ref                             []
% 3.94/0.98  --abstr_ref_prep                        false
% 3.94/0.98  --abstr_ref_until_sat                   false
% 3.94/0.98  --abstr_ref_sig_restrict                funpre
% 3.94/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.94/0.98  --abstr_ref_under                       []
% 3.94/0.98  
% 3.94/0.98  ------ SAT Options
% 3.94/0.98  
% 3.94/0.98  --sat_mode                              false
% 3.94/0.98  --sat_fm_restart_options                ""
% 3.94/0.98  --sat_gr_def                            false
% 3.94/0.98  --sat_epr_types                         true
% 3.94/0.98  --sat_non_cyclic_types                  false
% 3.94/0.98  --sat_finite_models                     false
% 3.94/0.98  --sat_fm_lemmas                         false
% 3.94/0.98  --sat_fm_prep                           false
% 3.94/0.98  --sat_fm_uc_incr                        true
% 3.94/0.98  --sat_out_model                         small
% 3.94/0.98  --sat_out_clauses                       false
% 3.94/0.98  
% 3.94/0.98  ------ QBF Options
% 3.94/0.98  
% 3.94/0.98  --qbf_mode                              false
% 3.94/0.98  --qbf_elim_univ                         false
% 3.94/0.98  --qbf_dom_inst                          none
% 3.94/0.98  --qbf_dom_pre_inst                      false
% 3.94/0.98  --qbf_sk_in                             false
% 3.94/0.98  --qbf_pred_elim                         true
% 3.94/0.98  --qbf_split                             512
% 3.94/0.98  
% 3.94/0.98  ------ BMC1 Options
% 3.94/0.98  
% 3.94/0.98  --bmc1_incremental                      false
% 3.94/0.98  --bmc1_axioms                           reachable_all
% 3.94/0.98  --bmc1_min_bound                        0
% 3.94/0.98  --bmc1_max_bound                        -1
% 3.94/0.98  --bmc1_max_bound_default                -1
% 3.94/0.98  --bmc1_symbol_reachability              true
% 3.94/0.98  --bmc1_property_lemmas                  false
% 3.94/0.98  --bmc1_k_induction                      false
% 3.94/0.98  --bmc1_non_equiv_states                 false
% 3.94/0.98  --bmc1_deadlock                         false
% 3.94/0.98  --bmc1_ucm                              false
% 3.94/0.98  --bmc1_add_unsat_core                   none
% 3.94/0.98  --bmc1_unsat_core_children              false
% 3.94/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.94/0.98  --bmc1_out_stat                         full
% 3.94/0.98  --bmc1_ground_init                      false
% 3.94/0.98  --bmc1_pre_inst_next_state              false
% 3.94/0.98  --bmc1_pre_inst_state                   false
% 3.94/0.98  --bmc1_pre_inst_reach_state             false
% 3.94/0.98  --bmc1_out_unsat_core                   false
% 3.94/0.98  --bmc1_aig_witness_out                  false
% 3.94/0.98  --bmc1_verbose                          false
% 3.94/0.98  --bmc1_dump_clauses_tptp                false
% 3.94/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.94/0.98  --bmc1_dump_file                        -
% 3.94/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.94/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.94/0.98  --bmc1_ucm_extend_mode                  1
% 3.94/0.98  --bmc1_ucm_init_mode                    2
% 3.94/0.98  --bmc1_ucm_cone_mode                    none
% 3.94/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.94/0.98  --bmc1_ucm_relax_model                  4
% 3.94/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.94/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.94/0.98  --bmc1_ucm_layered_model                none
% 3.94/0.98  --bmc1_ucm_max_lemma_size               10
% 3.94/0.98  
% 3.94/0.98  ------ AIG Options
% 3.94/0.98  
% 3.94/0.98  --aig_mode                              false
% 3.94/0.98  
% 3.94/0.98  ------ Instantiation Options
% 3.94/0.98  
% 3.94/0.98  --instantiation_flag                    true
% 3.94/0.98  --inst_sos_flag                         false
% 3.94/0.98  --inst_sos_phase                        true
% 3.94/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.94/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.94/0.98  --inst_lit_sel_side                     num_symb
% 3.94/0.98  --inst_solver_per_active                1400
% 3.94/0.98  --inst_solver_calls_frac                1.
% 3.94/0.98  --inst_passive_queue_type               priority_queues
% 3.94/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.94/0.98  --inst_passive_queues_freq              [25;2]
% 3.94/0.98  --inst_dismatching                      true
% 3.94/0.98  --inst_eager_unprocessed_to_passive     true
% 3.94/0.98  --inst_prop_sim_given                   true
% 3.94/0.98  --inst_prop_sim_new                     false
% 3.94/0.98  --inst_subs_new                         false
% 3.94/0.98  --inst_eq_res_simp                      false
% 3.94/0.98  --inst_subs_given                       false
% 3.94/0.98  --inst_orphan_elimination               true
% 3.94/0.98  --inst_learning_loop_flag               true
% 3.94/0.98  --inst_learning_start                   3000
% 3.94/0.98  --inst_learning_factor                  2
% 3.94/0.98  --inst_start_prop_sim_after_learn       3
% 3.94/0.98  --inst_sel_renew                        solver
% 3.94/0.98  --inst_lit_activity_flag                true
% 3.94/0.98  --inst_restr_to_given                   false
% 3.94/0.98  --inst_activity_threshold               500
% 3.94/0.98  --inst_out_proof                        true
% 3.94/0.98  
% 3.94/0.98  ------ Resolution Options
% 3.94/0.98  
% 3.94/0.98  --resolution_flag                       true
% 3.94/0.98  --res_lit_sel                           adaptive
% 3.94/0.98  --res_lit_sel_side                      none
% 3.94/0.98  --res_ordering                          kbo
% 3.94/0.98  --res_to_prop_solver                    active
% 3.94/0.98  --res_prop_simpl_new                    false
% 3.94/0.98  --res_prop_simpl_given                  true
% 3.94/0.98  --res_passive_queue_type                priority_queues
% 3.94/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.94/0.99  --res_passive_queues_freq               [15;5]
% 3.94/0.99  --res_forward_subs                      full
% 3.94/0.99  --res_backward_subs                     full
% 3.94/0.99  --res_forward_subs_resolution           true
% 3.94/0.99  --res_backward_subs_resolution          true
% 3.94/0.99  --res_orphan_elimination                true
% 3.94/0.99  --res_time_limit                        2.
% 3.94/0.99  --res_out_proof                         true
% 3.94/0.99  
% 3.94/0.99  ------ Superposition Options
% 3.94/0.99  
% 3.94/0.99  --superposition_flag                    true
% 3.94/0.99  --sup_passive_queue_type                priority_queues
% 3.94/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.94/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.94/0.99  --demod_completeness_check              fast
% 3.94/0.99  --demod_use_ground                      true
% 3.94/0.99  --sup_to_prop_solver                    passive
% 3.94/0.99  --sup_prop_simpl_new                    true
% 3.94/0.99  --sup_prop_simpl_given                  true
% 3.94/0.99  --sup_fun_splitting                     false
% 3.94/0.99  --sup_smt_interval                      50000
% 3.94/0.99  
% 3.94/0.99  ------ Superposition Simplification Setup
% 3.94/0.99  
% 3.94/0.99  --sup_indices_passive                   []
% 3.94/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.94/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.94/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.94/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.94/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.94/0.99  --sup_full_bw                           [BwDemod]
% 3.94/0.99  --sup_immed_triv                        [TrivRules]
% 3.94/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.94/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.94/0.99  --sup_immed_bw_main                     []
% 3.94/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.94/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.94/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.94/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.94/0.99  
% 3.94/0.99  ------ Combination Options
% 3.94/0.99  
% 3.94/0.99  --comb_res_mult                         3
% 3.94/0.99  --comb_sup_mult                         2
% 3.94/0.99  --comb_inst_mult                        10
% 3.94/0.99  
% 3.94/0.99  ------ Debug Options
% 3.94/0.99  
% 3.94/0.99  --dbg_backtrace                         false
% 3.94/0.99  --dbg_dump_prop_clauses                 false
% 3.94/0.99  --dbg_dump_prop_clauses_file            -
% 3.94/0.99  --dbg_out_stat                          false
% 3.94/0.99  ------ Parsing...
% 3.94/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.94/0.99  
% 3.94/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.94/0.99  
% 3.94/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.94/0.99  
% 3.94/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/0.99  ------ Proving...
% 3.94/0.99  ------ Problem Properties 
% 3.94/0.99  
% 3.94/0.99  
% 3.94/0.99  clauses                                 29
% 3.94/0.99  conjectures                             6
% 3.94/0.99  EPR                                     6
% 3.94/0.99  Horn                                    28
% 3.94/0.99  unary                                   14
% 3.94/0.99  binary                                  1
% 3.94/0.99  lits                                    75
% 3.94/0.99  lits eq                                 12
% 3.94/0.99  fd_pure                                 0
% 3.94/0.99  fd_pseudo                               0
% 3.94/0.99  fd_cond                                 3
% 3.94/0.99  fd_pseudo_cond                          1
% 3.94/0.99  AC symbols                              0
% 3.94/0.99  
% 3.94/0.99  ------ Schedule dynamic 5 is on 
% 3.94/0.99  
% 3.94/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.94/0.99  
% 3.94/0.99  
% 3.94/0.99  ------ 
% 3.94/0.99  Current options:
% 3.94/0.99  ------ 
% 3.94/0.99  
% 3.94/0.99  ------ Input Options
% 3.94/0.99  
% 3.94/0.99  --out_options                           all
% 3.94/0.99  --tptp_safe_out                         true
% 3.94/0.99  --problem_path                          ""
% 3.94/0.99  --include_path                          ""
% 3.94/0.99  --clausifier                            res/vclausify_rel
% 3.94/0.99  --clausifier_options                    --mode clausify
% 3.94/0.99  --stdin                                 false
% 3.94/0.99  --stats_out                             all
% 3.94/0.99  
% 3.94/0.99  ------ General Options
% 3.94/0.99  
% 3.94/0.99  --fof                                   false
% 3.94/0.99  --time_out_real                         305.
% 3.94/0.99  --time_out_virtual                      -1.
% 3.94/0.99  --symbol_type_check                     false
% 3.94/0.99  --clausify_out                          false
% 3.94/0.99  --sig_cnt_out                           false
% 3.94/0.99  --trig_cnt_out                          false
% 3.94/0.99  --trig_cnt_out_tolerance                1.
% 3.94/0.99  --trig_cnt_out_sk_spl                   false
% 3.94/0.99  --abstr_cl_out                          false
% 3.94/0.99  
% 3.94/0.99  ------ Global Options
% 3.94/0.99  
% 3.94/0.99  --schedule                              default
% 3.94/0.99  --add_important_lit                     false
% 3.94/0.99  --prop_solver_per_cl                    1000
% 3.94/0.99  --min_unsat_core                        false
% 3.94/0.99  --soft_assumptions                      false
% 3.94/0.99  --soft_lemma_size                       3
% 3.94/0.99  --prop_impl_unit_size                   0
% 3.94/0.99  --prop_impl_unit                        []
% 3.94/0.99  --share_sel_clauses                     true
% 3.94/0.99  --reset_solvers                         false
% 3.94/0.99  --bc_imp_inh                            [conj_cone]
% 3.94/0.99  --conj_cone_tolerance                   3.
% 3.94/0.99  --extra_neg_conj                        none
% 3.94/0.99  --large_theory_mode                     true
% 3.94/0.99  --prolific_symb_bound                   200
% 3.94/0.99  --lt_threshold                          2000
% 3.94/0.99  --clause_weak_htbl                      true
% 3.94/0.99  --gc_record_bc_elim                     false
% 3.94/0.99  
% 3.94/0.99  ------ Preprocessing Options
% 3.94/0.99  
% 3.94/0.99  --preprocessing_flag                    true
% 3.94/0.99  --time_out_prep_mult                    0.1
% 3.94/0.99  --splitting_mode                        input
% 3.94/0.99  --splitting_grd                         true
% 3.94/0.99  --splitting_cvd                         false
% 3.94/0.99  --splitting_cvd_svl                     false
% 3.94/0.99  --splitting_nvd                         32
% 3.94/0.99  --sub_typing                            true
% 3.94/0.99  --prep_gs_sim                           true
% 3.94/0.99  --prep_unflatten                        true
% 3.94/0.99  --prep_res_sim                          true
% 3.94/0.99  --prep_upred                            true
% 3.94/0.99  --prep_sem_filter                       exhaustive
% 3.94/0.99  --prep_sem_filter_out                   false
% 3.94/0.99  --pred_elim                             true
% 3.94/0.99  --res_sim_input                         true
% 3.94/0.99  --eq_ax_congr_red                       true
% 3.94/0.99  --pure_diseq_elim                       true
% 3.94/0.99  --brand_transform                       false
% 3.94/0.99  --non_eq_to_eq                          false
% 3.94/0.99  --prep_def_merge                        true
% 3.94/0.99  --prep_def_merge_prop_impl              false
% 3.94/0.99  --prep_def_merge_mbd                    true
% 3.94/0.99  --prep_def_merge_tr_red                 false
% 3.94/0.99  --prep_def_merge_tr_cl                  false
% 3.94/0.99  --smt_preprocessing                     true
% 3.94/0.99  --smt_ac_axioms                         fast
% 3.94/0.99  --preprocessed_out                      false
% 3.94/0.99  --preprocessed_stats                    false
% 3.94/0.99  
% 3.94/0.99  ------ Abstraction refinement Options
% 3.94/0.99  
% 3.94/0.99  --abstr_ref                             []
% 3.94/0.99  --abstr_ref_prep                        false
% 3.94/0.99  --abstr_ref_until_sat                   false
% 3.94/0.99  --abstr_ref_sig_restrict                funpre
% 3.94/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.94/0.99  --abstr_ref_under                       []
% 3.94/0.99  
% 3.94/0.99  ------ SAT Options
% 3.94/0.99  
% 3.94/0.99  --sat_mode                              false
% 3.94/0.99  --sat_fm_restart_options                ""
% 3.94/0.99  --sat_gr_def                            false
% 3.94/0.99  --sat_epr_types                         true
% 3.94/0.99  --sat_non_cyclic_types                  false
% 3.94/0.99  --sat_finite_models                     false
% 3.94/0.99  --sat_fm_lemmas                         false
% 3.94/0.99  --sat_fm_prep                           false
% 3.94/0.99  --sat_fm_uc_incr                        true
% 3.94/0.99  --sat_out_model                         small
% 3.94/0.99  --sat_out_clauses                       false
% 3.94/0.99  
% 3.94/0.99  ------ QBF Options
% 3.94/0.99  
% 3.94/0.99  --qbf_mode                              false
% 3.94/0.99  --qbf_elim_univ                         false
% 3.94/0.99  --qbf_dom_inst                          none
% 3.94/0.99  --qbf_dom_pre_inst                      false
% 3.94/0.99  --qbf_sk_in                             false
% 3.94/0.99  --qbf_pred_elim                         true
% 3.94/0.99  --qbf_split                             512
% 3.94/0.99  
% 3.94/0.99  ------ BMC1 Options
% 3.94/0.99  
% 3.94/0.99  --bmc1_incremental                      false
% 3.94/0.99  --bmc1_axioms                           reachable_all
% 3.94/0.99  --bmc1_min_bound                        0
% 3.94/0.99  --bmc1_max_bound                        -1
% 3.94/0.99  --bmc1_max_bound_default                -1
% 3.94/0.99  --bmc1_symbol_reachability              true
% 3.94/0.99  --bmc1_property_lemmas                  false
% 3.94/0.99  --bmc1_k_induction                      false
% 3.94/0.99  --bmc1_non_equiv_states                 false
% 3.94/0.99  --bmc1_deadlock                         false
% 3.94/0.99  --bmc1_ucm                              false
% 3.94/0.99  --bmc1_add_unsat_core                   none
% 3.94/0.99  --bmc1_unsat_core_children              false
% 3.94/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.94/0.99  --bmc1_out_stat                         full
% 3.94/0.99  --bmc1_ground_init                      false
% 3.94/0.99  --bmc1_pre_inst_next_state              false
% 3.94/0.99  --bmc1_pre_inst_state                   false
% 3.94/0.99  --bmc1_pre_inst_reach_state             false
% 3.94/0.99  --bmc1_out_unsat_core                   false
% 3.94/0.99  --bmc1_aig_witness_out                  false
% 3.94/0.99  --bmc1_verbose                          false
% 3.94/0.99  --bmc1_dump_clauses_tptp                false
% 3.94/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.94/0.99  --bmc1_dump_file                        -
% 3.94/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.94/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.94/0.99  --bmc1_ucm_extend_mode                  1
% 3.94/0.99  --bmc1_ucm_init_mode                    2
% 3.94/0.99  --bmc1_ucm_cone_mode                    none
% 3.94/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.94/0.99  --bmc1_ucm_relax_model                  4
% 3.94/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.94/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.94/0.99  --bmc1_ucm_layered_model                none
% 3.94/0.99  --bmc1_ucm_max_lemma_size               10
% 3.94/0.99  
% 3.94/0.99  ------ AIG Options
% 3.94/0.99  
% 3.94/0.99  --aig_mode                              false
% 3.94/0.99  
% 3.94/0.99  ------ Instantiation Options
% 3.94/0.99  
% 3.94/0.99  --instantiation_flag                    true
% 3.94/0.99  --inst_sos_flag                         false
% 3.94/0.99  --inst_sos_phase                        true
% 3.94/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.94/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.94/0.99  --inst_lit_sel_side                     none
% 3.94/0.99  --inst_solver_per_active                1400
% 3.94/0.99  --inst_solver_calls_frac                1.
% 3.94/0.99  --inst_passive_queue_type               priority_queues
% 3.94/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.94/0.99  --inst_passive_queues_freq              [25;2]
% 3.94/0.99  --inst_dismatching                      true
% 3.94/0.99  --inst_eager_unprocessed_to_passive     true
% 3.94/0.99  --inst_prop_sim_given                   true
% 3.94/0.99  --inst_prop_sim_new                     false
% 3.94/0.99  --inst_subs_new                         false
% 3.94/0.99  --inst_eq_res_simp                      false
% 3.94/0.99  --inst_subs_given                       false
% 3.94/0.99  --inst_orphan_elimination               true
% 3.94/0.99  --inst_learning_loop_flag               true
% 3.94/0.99  --inst_learning_start                   3000
% 3.94/0.99  --inst_learning_factor                  2
% 3.94/0.99  --inst_start_prop_sim_after_learn       3
% 3.94/0.99  --inst_sel_renew                        solver
% 3.94/0.99  --inst_lit_activity_flag                true
% 3.94/0.99  --inst_restr_to_given                   false
% 3.94/0.99  --inst_activity_threshold               500
% 3.94/0.99  --inst_out_proof                        true
% 3.94/0.99  
% 3.94/0.99  ------ Resolution Options
% 3.94/0.99  
% 3.94/0.99  --resolution_flag                       false
% 3.94/0.99  --res_lit_sel                           adaptive
% 3.94/0.99  --res_lit_sel_side                      none
% 3.94/0.99  --res_ordering                          kbo
% 3.94/0.99  --res_to_prop_solver                    active
% 3.94/0.99  --res_prop_simpl_new                    false
% 3.94/0.99  --res_prop_simpl_given                  true
% 3.94/0.99  --res_passive_queue_type                priority_queues
% 3.94/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.94/0.99  --res_passive_queues_freq               [15;5]
% 3.94/0.99  --res_forward_subs                      full
% 3.94/0.99  --res_backward_subs                     full
% 3.94/0.99  --res_forward_subs_resolution           true
% 3.94/0.99  --res_backward_subs_resolution          true
% 3.94/0.99  --res_orphan_elimination                true
% 3.94/0.99  --res_time_limit                        2.
% 3.94/0.99  --res_out_proof                         true
% 3.94/0.99  
% 3.94/0.99  ------ Superposition Options
% 3.94/0.99  
% 3.94/0.99  --superposition_flag                    true
% 3.94/0.99  --sup_passive_queue_type                priority_queues
% 3.94/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.94/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.94/0.99  --demod_completeness_check              fast
% 3.94/0.99  --demod_use_ground                      true
% 3.94/0.99  --sup_to_prop_solver                    passive
% 3.94/0.99  --sup_prop_simpl_new                    true
% 3.94/0.99  --sup_prop_simpl_given                  true
% 3.94/0.99  --sup_fun_splitting                     false
% 3.94/0.99  --sup_smt_interval                      50000
% 3.94/0.99  
% 3.94/0.99  ------ Superposition Simplification Setup
% 3.94/0.99  
% 3.94/0.99  --sup_indices_passive                   []
% 3.94/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.94/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.94/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.94/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.94/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.94/0.99  --sup_full_bw                           [BwDemod]
% 3.94/0.99  --sup_immed_triv                        [TrivRules]
% 3.94/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.94/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.94/0.99  --sup_immed_bw_main                     []
% 3.94/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.94/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.94/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.94/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.94/0.99  
% 3.94/0.99  ------ Combination Options
% 3.94/0.99  
% 3.94/0.99  --comb_res_mult                         3
% 3.94/0.99  --comb_sup_mult                         2
% 3.94/0.99  --comb_inst_mult                        10
% 3.94/0.99  
% 3.94/0.99  ------ Debug Options
% 3.94/0.99  
% 3.94/0.99  --dbg_backtrace                         false
% 3.94/0.99  --dbg_dump_prop_clauses                 false
% 3.94/0.99  --dbg_dump_prop_clauses_file            -
% 3.94/0.99  --dbg_out_stat                          false
% 3.94/0.99  
% 3.94/0.99  
% 3.94/0.99  
% 3.94/0.99  
% 3.94/0.99  ------ Proving...
% 3.94/0.99  
% 3.94/0.99  
% 3.94/0.99  % SZS status Theorem for theBenchmark.p
% 3.94/0.99  
% 3.94/0.99   Resolution empty clause
% 3.94/0.99  
% 3.94/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.94/0.99  
% 3.94/0.99  fof(f20,conjecture,(
% 3.94/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f21,negated_conjecture,(
% 3.94/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.94/0.99    inference(negated_conjecture,[],[f20])).
% 3.94/0.99  
% 3.94/0.99  fof(f40,plain,(
% 3.94/0.99    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.94/0.99    inference(ennf_transformation,[],[f21])).
% 3.94/0.99  
% 3.94/0.99  fof(f41,plain,(
% 3.94/0.99    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.94/0.99    inference(flattening,[],[f40])).
% 3.94/0.99  
% 3.94/0.99  fof(f49,plain,(
% 3.94/0.99    ( ! [X2,X0,X1] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 3.94/0.99    introduced(choice_axiom,[])).
% 3.94/0.99  
% 3.94/0.99  fof(f48,plain,(
% 3.94/0.99    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 3.94/0.99    introduced(choice_axiom,[])).
% 3.94/0.99  
% 3.94/0.99  fof(f50,plain,(
% 3.94/0.99    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 3.94/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f41,f49,f48])).
% 3.94/0.99  
% 3.94/0.99  fof(f84,plain,(
% 3.94/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.94/0.99    inference(cnf_transformation,[],[f50])).
% 3.94/0.99  
% 3.94/0.99  fof(f87,plain,(
% 3.94/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.94/0.99    inference(cnf_transformation,[],[f50])).
% 3.94/0.99  
% 3.94/0.99  fof(f17,axiom,(
% 3.94/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f36,plain,(
% 3.94/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.94/0.99    inference(ennf_transformation,[],[f17])).
% 3.94/0.99  
% 3.94/0.99  fof(f37,plain,(
% 3.94/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.94/0.99    inference(flattening,[],[f36])).
% 3.94/0.99  
% 3.94/0.99  fof(f78,plain,(
% 3.94/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.94/0.99    inference(cnf_transformation,[],[f37])).
% 3.94/0.99  
% 3.94/0.99  fof(f85,plain,(
% 3.94/0.99    v1_funct_1(sK3)),
% 3.94/0.99    inference(cnf_transformation,[],[f50])).
% 3.94/0.99  
% 3.94/0.99  fof(f82,plain,(
% 3.94/0.99    v1_funct_1(sK2)),
% 3.94/0.99    inference(cnf_transformation,[],[f50])).
% 3.94/0.99  
% 3.94/0.99  fof(f19,axiom,(
% 3.94/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 3.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f38,plain,(
% 3.94/0.99    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.94/0.99    inference(ennf_transformation,[],[f19])).
% 3.94/0.99  
% 3.94/0.99  fof(f39,plain,(
% 3.94/0.99    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.94/0.99    inference(flattening,[],[f38])).
% 3.94/0.99  
% 3.94/0.99  fof(f80,plain,(
% 3.94/0.99    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.94/0.99    inference(cnf_transformation,[],[f39])).
% 3.94/0.99  
% 3.94/0.99  fof(f83,plain,(
% 3.94/0.99    v1_funct_2(sK2,sK0,sK1)),
% 3.94/0.99    inference(cnf_transformation,[],[f50])).
% 3.94/0.99  
% 3.94/0.99  fof(f86,plain,(
% 3.94/0.99    v1_funct_2(sK3,sK1,sK0)),
% 3.94/0.99    inference(cnf_transformation,[],[f50])).
% 3.94/0.99  
% 3.94/0.99  fof(f11,axiom,(
% 3.94/0.99    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f67,plain,(
% 3.94/0.99    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.94/0.99    inference(cnf_transformation,[],[f11])).
% 3.94/0.99  
% 3.94/0.99  fof(f18,axiom,(
% 3.94/0.99    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f79,plain,(
% 3.94/0.99    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.94/0.99    inference(cnf_transformation,[],[f18])).
% 3.94/0.99  
% 3.94/0.99  fof(f94,plain,(
% 3.94/0.99    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 3.94/0.99    inference(definition_unfolding,[],[f67,f79])).
% 3.94/0.99  
% 3.94/0.99  fof(f68,plain,(
% 3.94/0.99    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 3.94/0.99    inference(cnf_transformation,[],[f11])).
% 3.94/0.99  
% 3.94/0.99  fof(f93,plain,(
% 3.94/0.99    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 3.94/0.99    inference(definition_unfolding,[],[f68,f79])).
% 3.94/0.99  
% 3.94/0.99  fof(f9,axiom,(
% 3.94/0.99    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f65,plain,(
% 3.94/0.99    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.94/0.99    inference(cnf_transformation,[],[f9])).
% 3.94/0.99  
% 3.94/0.99  fof(f90,plain,(
% 3.94/0.99    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 3.94/0.99    inference(definition_unfolding,[],[f65,f79])).
% 3.94/0.99  
% 3.94/0.99  fof(f1,axiom,(
% 3.94/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f42,plain,(
% 3.94/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.94/0.99    inference(nnf_transformation,[],[f1])).
% 3.94/0.99  
% 3.94/0.99  fof(f43,plain,(
% 3.94/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.94/0.99    inference(flattening,[],[f42])).
% 3.94/0.99  
% 3.94/0.99  fof(f51,plain,(
% 3.94/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.94/0.99    inference(cnf_transformation,[],[f43])).
% 3.94/0.99  
% 3.94/0.99  fof(f97,plain,(
% 3.94/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.94/0.99    inference(equality_resolution,[],[f51])).
% 3.94/0.99  
% 3.94/0.99  fof(f53,plain,(
% 3.94/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.94/0.99    inference(cnf_transformation,[],[f43])).
% 3.94/0.99  
% 3.94/0.99  fof(f4,axiom,(
% 3.94/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f24,plain,(
% 3.94/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.94/0.99    inference(ennf_transformation,[],[f4])).
% 3.94/0.99  
% 3.94/0.99  fof(f45,plain,(
% 3.94/0.99    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.94/0.99    inference(nnf_transformation,[],[f24])).
% 3.94/0.99  
% 3.94/0.99  fof(f58,plain,(
% 3.94/0.99    ( ! [X0,X1] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.94/0.99    inference(cnf_transformation,[],[f45])).
% 3.94/0.99  
% 3.94/0.99  fof(f15,axiom,(
% 3.94/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f32,plain,(
% 3.94/0.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.94/0.99    inference(ennf_transformation,[],[f15])).
% 3.94/0.99  
% 3.94/0.99  fof(f33,plain,(
% 3.94/0.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.94/0.99    inference(flattening,[],[f32])).
% 3.94/0.99  
% 3.94/0.99  fof(f47,plain,(
% 3.94/0.99    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.94/0.99    inference(nnf_transformation,[],[f33])).
% 3.94/0.99  
% 3.94/0.99  fof(f75,plain,(
% 3.94/0.99    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.94/0.99    inference(cnf_transformation,[],[f47])).
% 3.94/0.99  
% 3.94/0.99  fof(f99,plain,(
% 3.94/0.99    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.94/0.99    inference(equality_resolution,[],[f75])).
% 3.94/0.99  
% 3.94/0.99  fof(f89,plain,(
% 3.94/0.99    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 3.94/0.99    inference(cnf_transformation,[],[f50])).
% 3.94/0.99  
% 3.94/0.99  fof(f52,plain,(
% 3.94/0.99    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.94/0.99    inference(cnf_transformation,[],[f43])).
% 3.94/0.99  
% 3.94/0.99  fof(f96,plain,(
% 3.94/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.94/0.99    inference(equality_resolution,[],[f52])).
% 3.94/0.99  
% 3.94/0.99  fof(f8,axiom,(
% 3.94/0.99    ! [X0] : (v1_relat_1(X0) => ((k2_relat_1(X0) = k1_xboole_0 | k1_relat_1(X0) = k1_xboole_0) => k1_xboole_0 = X0))),
% 3.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f27,plain,(
% 3.94/0.99    ! [X0] : ((k1_xboole_0 = X0 | (k2_relat_1(X0) != k1_xboole_0 & k1_relat_1(X0) != k1_xboole_0)) | ~v1_relat_1(X0))),
% 3.94/0.99    inference(ennf_transformation,[],[f8])).
% 3.94/0.99  
% 3.94/0.99  fof(f28,plain,(
% 3.94/0.99    ! [X0] : (k1_xboole_0 = X0 | (k2_relat_1(X0) != k1_xboole_0 & k1_relat_1(X0) != k1_xboole_0) | ~v1_relat_1(X0))),
% 3.94/0.99    inference(flattening,[],[f27])).
% 3.94/0.99  
% 3.94/0.99  fof(f62,plain,(
% 3.94/0.99    ( ! [X0] : (k1_xboole_0 = X0 | k1_relat_1(X0) != k1_xboole_0 | ~v1_relat_1(X0)) )),
% 3.94/0.99    inference(cnf_transformation,[],[f28])).
% 3.94/0.99  
% 3.94/0.99  fof(f63,plain,(
% 3.94/0.99    ( ! [X0] : (k1_xboole_0 = X0 | k2_relat_1(X0) != k1_xboole_0 | ~v1_relat_1(X0)) )),
% 3.94/0.99    inference(cnf_transformation,[],[f28])).
% 3.94/0.99  
% 3.94/0.99  fof(f12,axiom,(
% 3.94/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f29,plain,(
% 3.94/0.99    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.94/0.99    inference(ennf_transformation,[],[f12])).
% 3.94/0.99  
% 3.94/0.99  fof(f70,plain,(
% 3.94/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.94/0.99    inference(cnf_transformation,[],[f29])).
% 3.94/0.99  
% 3.94/0.99  fof(f57,plain,(
% 3.94/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.94/0.99    inference(cnf_transformation,[],[f45])).
% 3.94/0.99  
% 3.94/0.99  fof(f2,axiom,(
% 3.94/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f22,plain,(
% 3.94/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.94/0.99    inference(ennf_transformation,[],[f2])).
% 3.94/0.99  
% 3.94/0.99  fof(f54,plain,(
% 3.94/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.94/0.99    inference(cnf_transformation,[],[f22])).
% 3.94/0.99  
% 3.94/0.99  fof(f5,axiom,(
% 3.94/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f59,plain,(
% 3.94/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.94/0.99    inference(cnf_transformation,[],[f5])).
% 3.94/0.99  
% 3.94/0.99  fof(f69,plain,(
% 3.94/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.94/0.99    inference(cnf_transformation,[],[f29])).
% 3.94/0.99  
% 3.94/0.99  fof(f3,axiom,(
% 3.94/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f23,plain,(
% 3.94/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.94/0.99    inference(ennf_transformation,[],[f3])).
% 3.94/0.99  
% 3.94/0.99  fof(f44,plain,(
% 3.94/0.99    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.94/0.99    inference(nnf_transformation,[],[f23])).
% 3.94/0.99  
% 3.94/0.99  fof(f55,plain,(
% 3.94/0.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.94/0.99    inference(cnf_transformation,[],[f44])).
% 3.94/0.99  
% 3.94/0.99  fof(f13,axiom,(
% 3.94/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f30,plain,(
% 3.94/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.94/0.99    inference(ennf_transformation,[],[f13])).
% 3.94/0.99  
% 3.94/0.99  fof(f31,plain,(
% 3.94/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.94/0.99    inference(flattening,[],[f30])).
% 3.94/0.99  
% 3.94/0.99  fof(f46,plain,(
% 3.94/0.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.94/0.99    inference(nnf_transformation,[],[f31])).
% 3.94/0.99  
% 3.94/0.99  fof(f71,plain,(
% 3.94/0.99    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.94/0.99    inference(cnf_transformation,[],[f46])).
% 3.94/0.99  
% 3.94/0.99  fof(f88,plain,(
% 3.94/0.99    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 3.94/0.99    inference(cnf_transformation,[],[f50])).
% 3.94/0.99  
% 3.94/0.99  fof(f14,axiom,(
% 3.94/0.99    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f73,plain,(
% 3.94/0.99    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.94/0.99    inference(cnf_transformation,[],[f14])).
% 3.94/0.99  
% 3.94/0.99  fof(f95,plain,(
% 3.94/0.99    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.94/0.99    inference(definition_unfolding,[],[f73,f79])).
% 3.94/0.99  
% 3.94/0.99  fof(f16,axiom,(
% 3.94/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f34,plain,(
% 3.94/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.94/0.99    inference(ennf_transformation,[],[f16])).
% 3.94/0.99  
% 3.94/0.99  fof(f35,plain,(
% 3.94/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.94/0.99    inference(flattening,[],[f34])).
% 3.94/0.99  
% 3.94/0.99  fof(f77,plain,(
% 3.94/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.94/0.99    inference(cnf_transformation,[],[f35])).
% 3.94/0.99  
% 3.94/0.99  fof(f7,axiom,(
% 3.94/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 3.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f26,plain,(
% 3.94/0.99    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.94/0.99    inference(ennf_transformation,[],[f7])).
% 3.94/0.99  
% 3.94/0.99  fof(f61,plain,(
% 3.94/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.94/0.99    inference(cnf_transformation,[],[f26])).
% 3.94/0.99  
% 3.94/0.99  fof(f6,axiom,(
% 3.94/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 3.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f25,plain,(
% 3.94/0.99    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.94/0.99    inference(ennf_transformation,[],[f6])).
% 3.94/0.99  
% 3.94/0.99  fof(f60,plain,(
% 3.94/0.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.94/0.99    inference(cnf_transformation,[],[f25])).
% 3.94/0.99  
% 3.94/0.99  fof(f64,plain,(
% 3.94/0.99    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.94/0.99    inference(cnf_transformation,[],[f9])).
% 3.94/0.99  
% 3.94/0.99  fof(f91,plain,(
% 3.94/0.99    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 3.94/0.99    inference(definition_unfolding,[],[f64,f79])).
% 3.94/0.99  
% 3.94/0.99  cnf(c_35,negated_conjecture,
% 3.94/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.94/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1156,plain,
% 3.94/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_32,negated_conjecture,
% 3.94/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.94/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1159,plain,
% 3.94/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_27,plain,
% 3.94/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.94/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.94/0.99      | ~ v1_funct_1(X0)
% 3.94/0.99      | ~ v1_funct_1(X3)
% 3.94/0.99      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.94/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1162,plain,
% 3.94/0.99      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.94/0.99      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.94/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.94/0.99      | v1_funct_1(X5) != iProver_top
% 3.94/0.99      | v1_funct_1(X4) != iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_3842,plain,
% 3.94/0.99      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 3.94/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.94/0.99      | v1_funct_1(X2) != iProver_top
% 3.94/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_1159,c_1162]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_34,negated_conjecture,
% 3.94/0.99      ( v1_funct_1(sK3) ),
% 3.94/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_41,plain,
% 3.94/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_4157,plain,
% 3.94/0.99      ( v1_funct_1(X2) != iProver_top
% 3.94/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.94/0.99      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 3.94/0.99      inference(global_propositional_subsumption,[status(thm)],[c_3842,c_41]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_4158,plain,
% 3.94/0.99      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 3.94/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.94/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.94/0.99      inference(renaming,[status(thm)],[c_4157]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_4169,plain,
% 3.94/0.99      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 3.94/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_1156,c_4158]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_37,negated_conjecture,
% 3.94/0.99      ( v1_funct_1(sK2) ),
% 3.94/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1496,plain,
% 3.94/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.94/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 3.94/0.99      | ~ v1_funct_1(X0)
% 3.94/0.99      | ~ v1_funct_1(sK3)
% 3.94/0.99      | k1_partfun1(X1,X2,X3,X4,X0,sK3) = k5_relat_1(X0,sK3) ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_27]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1794,plain,
% 3.94/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.94/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.94/0.99      | ~ v1_funct_1(sK2)
% 3.94/0.99      | ~ v1_funct_1(sK3)
% 3.94/0.99      | k1_partfun1(X0,X1,X2,X3,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_1496]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_2269,plain,
% 3.94/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.94/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.94/0.99      | ~ v1_funct_1(sK2)
% 3.94/0.99      | ~ v1_funct_1(sK3)
% 3.94/0.99      | k1_partfun1(sK0,sK1,X0,X1,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_1794]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_3485,plain,
% 3.94/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.94/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.94/0.99      | ~ v1_funct_1(sK2)
% 3.94/0.99      | ~ v1_funct_1(sK3)
% 3.94/0.99      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_2269]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_4294,plain,
% 3.94/0.99      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 3.94/0.99      inference(global_propositional_subsumption,
% 3.94/0.99                [status(thm)],
% 3.94/0.99                [c_4169,c_37,c_35,c_34,c_32,c_3485]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_29,plain,
% 3.94/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.94/0.99      | ~ v1_funct_2(X3,X4,X1)
% 3.94/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 3.94/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.94/0.99      | ~ v1_funct_1(X0)
% 3.94/0.99      | ~ v1_funct_1(X3)
% 3.94/0.99      | v2_funct_1(X3)
% 3.94/0.99      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 3.94/0.99      | k1_xboole_0 = X2 ),
% 3.94/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1160,plain,
% 3.94/0.99      ( k1_xboole_0 = X0
% 3.94/0.99      | v1_funct_2(X1,X2,X0) != iProver_top
% 3.94/0.99      | v1_funct_2(X3,X4,X2) != iProver_top
% 3.94/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 3.94/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 3.94/0.99      | v1_funct_1(X1) != iProver_top
% 3.94/0.99      | v1_funct_1(X3) != iProver_top
% 3.94/0.99      | v2_funct_1(X3) = iProver_top
% 3.94/0.99      | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_4301,plain,
% 3.94/0.99      ( sK0 = k1_xboole_0
% 3.94/0.99      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.94/0.99      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.94/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.94/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.94/0.99      | v1_funct_1(sK2) != iProver_top
% 3.94/0.99      | v1_funct_1(sK3) != iProver_top
% 3.94/0.99      | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
% 3.94/0.99      | v2_funct_1(sK2) = iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_4294,c_1160]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_38,plain,
% 3.94/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_36,negated_conjecture,
% 3.94/0.99      ( v1_funct_2(sK2,sK0,sK1) ),
% 3.94/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_39,plain,
% 3.94/0.99      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_40,plain,
% 3.94/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_33,negated_conjecture,
% 3.94/0.99      ( v1_funct_2(sK3,sK1,sK0) ),
% 3.94/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_42,plain,
% 3.94/0.99      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_43,plain,
% 3.94/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_17,plain,
% 3.94/0.99      ( v1_relat_1(k6_partfun1(X0)) ),
% 3.94/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_83,plain,
% 3.94/0.99      ( v1_relat_1(k6_partfun1(k1_xboole_0)) ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_17]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_16,plain,
% 3.94/0.99      ( v2_funct_1(k6_partfun1(X0)) ),
% 3.94/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_85,plain,
% 3.94/0.99      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_87,plain,
% 3.94/0.99      ( v2_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_85]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_13,plain,
% 3.94/0.99      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 3.94/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_89,plain,
% 3.94/0.99      ( k2_relat_1(k6_partfun1(k1_xboole_0)) = k1_xboole_0 ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_2,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f97]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_119,plain,
% 3.94/0.99      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_0,plain,
% 3.94/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.94/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_123,plain,
% 3.94/0.99      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_xboole_0 ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_6,plain,
% 3.94/0.99      ( v5_relat_1(X0,X1) | ~ r1_tarski(k2_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 3.94/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_23,plain,
% 3.94/0.99      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.94/0.99      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 3.94/0.99      | ~ v1_relat_1(X0) ),
% 3.94/0.99      inference(cnf_transformation,[],[f99]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_30,negated_conjecture,
% 3.94/0.99      ( ~ v2_funct_2(sK3,sK0) | ~ v2_funct_1(sK2) ),
% 3.94/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_427,plain,
% 3.94/0.99      ( ~ v5_relat_1(X0,k2_relat_1(X0))
% 3.94/0.99      | ~ v2_funct_1(sK2)
% 3.94/0.99      | ~ v1_relat_1(X0)
% 3.94/0.99      | k2_relat_1(X0) != sK0
% 3.94/0.99      | sK3 != X0 ),
% 3.94/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_30]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_428,plain,
% 3.94/0.99      ( ~ v5_relat_1(sK3,k2_relat_1(sK3))
% 3.94/0.99      | ~ v2_funct_1(sK2)
% 3.94/0.99      | ~ v1_relat_1(sK3)
% 3.94/0.99      | k2_relat_1(sK3) != sK0 ),
% 3.94/0.99      inference(unflattening,[status(thm)],[c_427]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_481,plain,
% 3.94/0.99      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 3.94/0.99      | ~ v2_funct_1(sK2)
% 3.94/0.99      | ~ v1_relat_1(X0)
% 3.94/0.99      | ~ v1_relat_1(sK3)
% 3.94/0.99      | k2_relat_1(sK3) != X1
% 3.94/0.99      | k2_relat_1(sK3) != sK0
% 3.94/0.99      | sK3 != X0 ),
% 3.94/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_428]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_482,plain,
% 3.94/0.99      ( ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(sK3))
% 3.94/0.99      | ~ v2_funct_1(sK2)
% 3.94/0.99      | ~ v1_relat_1(sK3)
% 3.94/0.99      | k2_relat_1(sK3) != sK0 ),
% 3.94/0.99      inference(unflattening,[status(thm)],[c_481]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f96]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_492,plain,
% 3.94/0.99      ( ~ v2_funct_1(sK2) | ~ v1_relat_1(sK3) | k2_relat_1(sK3) != sK0 ),
% 3.94/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_482,c_1]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_493,plain,
% 3.94/0.99      ( k2_relat_1(sK3) != sK0
% 3.94/0.99      | v2_funct_1(sK2) != iProver_top
% 3.94/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_492]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_688,plain,
% 3.94/0.99      ( ~ v2_funct_1(X0) | v2_funct_1(X1) | X1 != X0 ),
% 3.94/0.99      theory(equality) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1398,plain,
% 3.94/0.99      ( v2_funct_1(X0)
% 3.94/0.99      | ~ v2_funct_1(k6_partfun1(X1))
% 3.94/0.99      | X0 != k6_partfun1(X1) ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_688]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1399,plain,
% 3.94/0.99      ( X0 != k6_partfun1(X1)
% 3.94/0.99      | v2_funct_1(X0) = iProver_top
% 3.94/0.99      | v2_funct_1(k6_partfun1(X1)) != iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_1398]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1401,plain,
% 3.94/0.99      ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
% 3.94/0.99      | v2_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
% 3.94/0.99      | v2_funct_1(k1_xboole_0) = iProver_top ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_1399]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_12,plain,
% 3.94/0.99      ( ~ v1_relat_1(X0) | k1_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 3.94/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1575,plain,
% 3.94/0.99      ( ~ v1_relat_1(sK2)
% 3.94/0.99      | k1_relat_1(sK2) != k1_xboole_0
% 3.94/0.99      | k1_xboole_0 = sK2 ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_678,plain,( X0 = X0 ),theory(equality) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1647,plain,
% 3.94/0.99      ( sK2 = sK2 ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_678]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_11,plain,
% 3.94/0.99      ( ~ v1_relat_1(X0) | k2_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 3.94/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1747,plain,
% 3.94/0.99      ( ~ v1_relat_1(k6_partfun1(X0))
% 3.94/0.99      | k2_relat_1(k6_partfun1(X0)) != k1_xboole_0
% 3.94/0.99      | k1_xboole_0 = k6_partfun1(X0) ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1751,plain,
% 3.94/0.99      ( ~ v1_relat_1(k6_partfun1(k1_xboole_0))
% 3.94/0.99      | k2_relat_1(k6_partfun1(k1_xboole_0)) != k1_xboole_0
% 3.94/0.99      | k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_1747]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_679,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_2600,plain,
% 3.94/0.99      ( X0 != X1 | X0 = sK0 | sK0 != X1 ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_679]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_2601,plain,
% 3.94/0.99      ( sK0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 != k1_xboole_0 ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_2600]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_18,plain,
% 3.94/0.99      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.94/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_7,plain,
% 3.94/0.99      ( ~ v5_relat_1(X0,X1) | r1_tarski(k2_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 3.94/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_448,plain,
% 3.94/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.94/0.99      | r1_tarski(k2_relat_1(X0),X2)
% 3.94/0.99      | ~ v1_relat_1(X0) ),
% 3.94/0.99      inference(resolution,[status(thm)],[c_18,c_7]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1151,plain,
% 3.94/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.94/0.99      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 3.94/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_448]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_2521,plain,
% 3.94/0.99      ( r1_tarski(k2_relat_1(sK3),sK0) = iProver_top
% 3.94/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_1159,c_1151]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1175,plain,
% 3.94/0.99      ( X0 = X1
% 3.94/0.99      | r1_tarski(X0,X1) != iProver_top
% 3.94/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_2741,plain,
% 3.94/0.99      ( k2_relat_1(sK3) = sK0
% 3.94/0.99      | r1_tarski(sK0,k2_relat_1(sK3)) != iProver_top
% 3.94/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_2521,c_1175]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_3,plain,
% 3.94/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.94/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1173,plain,
% 3.94/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.94/0.99      | v1_relat_1(X1) != iProver_top
% 3.94/0.99      | v1_relat_1(X0) = iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_2973,plain,
% 3.94/0.99      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 3.94/0.99      | v1_relat_1(sK3) = iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_1159,c_1173]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_8,plain,
% 3.94/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.94/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1172,plain,
% 3.94/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_2989,plain,
% 3.94/0.99      ( v1_relat_1(sK3) = iProver_top ),
% 3.94/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_2973,c_1172]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_3021,plain,
% 3.94/0.99      ( ~ v2_funct_1(X0) | v2_funct_1(sK2) | sK2 != X0 ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_688]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_3022,plain,
% 3.94/0.99      ( sK2 != X0
% 3.94/0.99      | v2_funct_1(X0) != iProver_top
% 3.94/0.99      | v2_funct_1(sK2) = iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_3021]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_3024,plain,
% 3.94/0.99      ( sK2 != k1_xboole_0
% 3.94/0.99      | v2_funct_1(sK2) = iProver_top
% 3.94/0.99      | v2_funct_1(k1_xboole_0) != iProver_top ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_3022]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_2974,plain,
% 3.94/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.94/0.99      | v1_relat_1(sK2) = iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_1156,c_1173]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_3146,plain,
% 3.94/0.99      ( v1_relat_1(sK2) = iProver_top ),
% 3.94/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_2974,c_1172]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_3147,plain,
% 3.94/0.99      ( v1_relat_1(sK2) ),
% 3.94/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3146]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_19,plain,
% 3.94/0.99      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.94/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_5,plain,
% 3.94/0.99      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 3.94/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_388,plain,
% 3.94/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.94/0.99      | r1_tarski(k1_relat_1(X0),X1)
% 3.94/0.99      | ~ v1_relat_1(X0) ),
% 3.94/0.99      inference(resolution,[status(thm)],[c_19,c_5]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1153,plain,
% 3.94/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.94/0.99      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 3.94/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_388]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_3154,plain,
% 3.94/0.99      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top
% 3.94/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_1156,c_1153]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_2715,plain,
% 3.94/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.94/0.99      | r1_tarski(k1_relat_1(sK2),sK0)
% 3.94/0.99      | ~ v1_relat_1(sK2) ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_388]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_2716,plain,
% 3.94/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.94/0.99      | r1_tarski(k1_relat_1(sK2),sK0) = iProver_top
% 3.94/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_2715]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_3544,plain,
% 3.94/0.99      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
% 3.94/0.99      inference(global_propositional_subsumption,
% 3.94/0.99                [status(thm)],
% 3.94/0.99                [c_3154,c_40,c_2716,c_3146]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_3549,plain,
% 3.94/0.99      ( k1_relat_1(sK2) = sK0 | r1_tarski(sK0,k1_relat_1(sK2)) != iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_3544,c_1175]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_2560,plain,
% 3.94/0.99      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_679]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_4775,plain,
% 3.94/0.99      ( X0 != sK2 | sK2 = X0 | sK2 != sK2 ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_2560]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_4776,plain,
% 3.94/0.99      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_4775]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_21,plain,
% 3.94/0.99      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.94/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.94/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.94/0.99      | X3 = X2 ),
% 3.94/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_31,negated_conjecture,
% 3.94/0.99      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 3.94/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_409,plain,
% 3.94/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.94/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.94/0.99      | X3 = X0
% 3.94/0.99      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 3.94/0.99      | k6_partfun1(sK0) != X3
% 3.94/0.99      | sK0 != X2
% 3.94/0.99      | sK0 != X1 ),
% 3.94/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_31]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_410,plain,
% 3.94/0.99      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.94/0.99      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.94/0.99      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.94/0.99      inference(unflattening,[status(thm)],[c_409]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_22,plain,
% 3.94/0.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.94/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_418,plain,
% 3.94/0.99      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.94/0.99      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.94/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_410,c_22]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1152,plain,
% 3.94/0.99      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.94/0.99      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_418]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_4297,plain,
% 3.94/0.99      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 3.94/0.99      | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.94/0.99      inference(demodulation,[status(thm)],[c_4294,c_1152]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_25,plain,
% 3.94/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.94/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.94/0.99      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.94/0.99      | ~ v1_funct_1(X0)
% 3.94/0.99      | ~ v1_funct_1(X3) ),
% 3.94/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1164,plain,
% 3.94/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.94/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 3.94/0.99      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 3.94/0.99      | v1_funct_1(X0) != iProver_top
% 3.94/0.99      | v1_funct_1(X3) != iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_4299,plain,
% 3.94/0.99      ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 3.94/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.94/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.94/0.99      | v1_funct_1(sK2) != iProver_top
% 3.94/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_4294,c_1164]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_4966,plain,
% 3.94/0.99      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 3.94/0.99      inference(global_propositional_subsumption,
% 3.94/0.99                [status(thm)],
% 3.94/0.99                [c_4297,c_38,c_40,c_41,c_43,c_4299]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_10,plain,
% 3.94/0.99      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 3.94/0.99      | ~ v1_relat_1(X0)
% 3.94/0.99      | ~ v1_relat_1(X1) ),
% 3.94/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1170,plain,
% 3.94/0.99      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
% 3.94/0.99      | v1_relat_1(X0) != iProver_top
% 3.94/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_4971,plain,
% 3.94/0.99      ( r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(sK3)) = iProver_top
% 3.94/0.99      | v1_relat_1(sK2) != iProver_top
% 3.94/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_4966,c_1170]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_4975,plain,
% 3.94/0.99      ( r1_tarski(sK0,k2_relat_1(sK3)) = iProver_top
% 3.94/0.99      | v1_relat_1(sK2) != iProver_top
% 3.94/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.94/0.99      inference(demodulation,[status(thm)],[c_4971,c_13]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_9,plain,
% 3.94/0.99      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
% 3.94/0.99      | ~ v1_relat_1(X0)
% 3.94/0.99      | ~ v1_relat_1(X1) ),
% 3.94/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1171,plain,
% 3.94/0.99      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
% 3.94/0.99      | v1_relat_1(X0) != iProver_top
% 3.94/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_4970,plain,
% 3.94/0.99      ( r1_tarski(k1_relat_1(k6_partfun1(sK0)),k1_relat_1(sK2)) = iProver_top
% 3.94/0.99      | v1_relat_1(sK2) != iProver_top
% 3.94/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_4966,c_1171]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_14,plain,
% 3.94/0.99      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 3.94/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_4982,plain,
% 3.94/0.99      ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top
% 3.94/0.99      | v1_relat_1(sK2) != iProver_top
% 3.94/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.94/0.99      inference(demodulation,[status(thm)],[c_4970,c_14]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_3685,plain,
% 3.94/0.99      ( k1_relat_1(sK2) != X0
% 3.94/0.99      | k1_relat_1(sK2) = k1_xboole_0
% 3.94/0.99      | k1_xboole_0 != X0 ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_679]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_14547,plain,
% 3.94/0.99      ( k1_relat_1(sK2) != sK0
% 3.94/0.99      | k1_relat_1(sK2) = k1_xboole_0
% 3.94/0.99      | k1_xboole_0 != sK0 ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_3685]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_16315,plain,
% 3.94/0.99      ( v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top ),
% 3.94/0.99      inference(global_propositional_subsumption,
% 3.94/0.99                [status(thm)],
% 3.94/0.99                [c_4301,c_38,c_39,c_40,c_41,c_42,c_43,c_83,c_87,c_89,c_119,
% 3.94/0.99                 c_123,c_493,c_1401,c_1575,c_1647,c_1751,c_2601,c_2741,
% 3.94/0.99                 c_2989,c_3024,c_3146,c_3147,c_3549,c_4776,c_4975,c_4982,
% 3.94/0.99                 c_14547]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_16319,plain,
% 3.94/0.99      ( v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
% 3.94/0.99      inference(light_normalisation,[status(thm)],[c_16315,c_4966]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1167,plain,
% 3.94/0.99      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_16321,plain,
% 3.94/0.99      ( $false ),
% 3.94/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_16319,c_1167]) ).
% 3.94/0.99  
% 3.94/0.99  
% 3.94/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.94/0.99  
% 3.94/0.99  ------                               Statistics
% 3.94/0.99  
% 3.94/0.99  ------ General
% 3.94/0.99  
% 3.94/0.99  abstr_ref_over_cycles:                  0
% 3.94/0.99  abstr_ref_under_cycles:                 0
% 3.94/0.99  gc_basic_clause_elim:                   0
% 3.94/0.99  forced_gc_time:                         0
% 3.94/0.99  parsing_time:                           0.012
% 3.94/0.99  unif_index_cands_time:                  0.
% 3.94/0.99  unif_index_add_time:                    0.
% 3.94/0.99  orderings_time:                         0.
% 3.94/0.99  out_proof_time:                         0.015
% 3.94/0.99  total_time:                             0.488
% 3.94/0.99  num_of_symbols:                         53
% 3.94/0.99  num_of_terms:                           18597
% 3.94/0.99  
% 3.94/0.99  ------ Preprocessing
% 3.94/0.99  
% 3.94/0.99  num_of_splits:                          0
% 3.94/0.99  num_of_split_atoms:                     0
% 3.94/0.99  num_of_reused_defs:                     0
% 3.94/0.99  num_eq_ax_congr_red:                    9
% 3.94/0.99  num_of_sem_filtered_clauses:            1
% 3.94/0.99  num_of_subtypes:                        0
% 3.94/0.99  monotx_restored_types:                  0
% 3.94/0.99  sat_num_of_epr_types:                   0
% 3.94/0.99  sat_num_of_non_cyclic_types:            0
% 3.94/0.99  sat_guarded_non_collapsed_types:        0
% 3.94/0.99  num_pure_diseq_elim:                    0
% 3.94/0.99  simp_replaced_by:                       0
% 3.94/0.99  res_preprocessed:                       153
% 3.94/0.99  prep_upred:                             0
% 3.94/0.99  prep_unflattend:                        15
% 3.94/0.99  smt_new_axioms:                         0
% 3.94/0.99  pred_elim_cands:                        6
% 3.94/0.99  pred_elim:                              4
% 3.94/0.99  pred_elim_cl:                           8
% 3.94/0.99  pred_elim_cycles:                       6
% 3.94/0.99  merged_defs:                            0
% 3.94/0.99  merged_defs_ncl:                        0
% 3.94/0.99  bin_hyper_res:                          0
% 3.94/0.99  prep_cycles:                            4
% 3.94/0.99  pred_elim_time:                         0.004
% 3.94/0.99  splitting_time:                         0.
% 3.94/0.99  sem_filter_time:                        0.
% 3.94/0.99  monotx_time:                            0.001
% 3.94/0.99  subtype_inf_time:                       0.
% 3.94/0.99  
% 3.94/0.99  ------ Problem properties
% 3.94/0.99  
% 3.94/0.99  clauses:                                29
% 3.94/0.99  conjectures:                            6
% 3.94/0.99  epr:                                    6
% 3.94/0.99  horn:                                   28
% 3.94/0.99  ground:                                 9
% 3.94/0.99  unary:                                  14
% 3.94/0.99  binary:                                 1
% 3.94/0.99  lits:                                   75
% 3.94/0.99  lits_eq:                                12
% 3.94/0.99  fd_pure:                                0
% 3.94/0.99  fd_pseudo:                              0
% 3.94/0.99  fd_cond:                                3
% 3.94/0.99  fd_pseudo_cond:                         1
% 3.94/0.99  ac_symbols:                             0
% 3.94/0.99  
% 3.94/0.99  ------ Propositional Solver
% 3.94/0.99  
% 3.94/0.99  prop_solver_calls:                      29
% 3.94/0.99  prop_fast_solver_calls:                 1505
% 3.94/0.99  smt_solver_calls:                       0
% 3.94/0.99  smt_fast_solver_calls:                  0
% 3.94/0.99  prop_num_of_clauses:                    7116
% 3.94/0.99  prop_preprocess_simplified:             15411
% 3.94/0.99  prop_fo_subsumed:                       122
% 3.94/0.99  prop_solver_time:                       0.
% 3.94/0.99  smt_solver_time:                        0.
% 3.94/0.99  smt_fast_solver_time:                   0.
% 3.94/0.99  prop_fast_solver_time:                  0.
% 3.94/0.99  prop_unsat_core_time:                   0.
% 3.94/0.99  
% 3.94/0.99  ------ QBF
% 3.94/0.99  
% 3.94/0.99  qbf_q_res:                              0
% 3.94/0.99  qbf_num_tautologies:                    0
% 3.94/0.99  qbf_prep_cycles:                        0
% 3.94/0.99  
% 3.94/0.99  ------ BMC1
% 3.94/0.99  
% 3.94/0.99  bmc1_current_bound:                     -1
% 3.94/0.99  bmc1_last_solved_bound:                 -1
% 3.94/0.99  bmc1_unsat_core_size:                   -1
% 3.94/0.99  bmc1_unsat_core_parents_size:           -1
% 3.94/0.99  bmc1_merge_next_fun:                    0
% 3.94/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.94/0.99  
% 3.94/0.99  ------ Instantiation
% 3.94/0.99  
% 3.94/0.99  inst_num_of_clauses:                    1842
% 3.94/0.99  inst_num_in_passive:                    734
% 3.94/0.99  inst_num_in_active:                     814
% 3.94/0.99  inst_num_in_unprocessed:                296
% 3.94/0.99  inst_num_of_loops:                      860
% 3.94/0.99  inst_num_of_learning_restarts:          0
% 3.94/0.99  inst_num_moves_active_passive:          45
% 3.94/0.99  inst_lit_activity:                      0
% 3.94/0.99  inst_lit_activity_moves:                1
% 3.94/0.99  inst_num_tautologies:                   0
% 3.94/0.99  inst_num_prop_implied:                  0
% 3.94/0.99  inst_num_existing_simplified:           0
% 3.94/0.99  inst_num_eq_res_simplified:             0
% 3.94/0.99  inst_num_child_elim:                    0
% 3.94/0.99  inst_num_of_dismatching_blockings:      306
% 3.94/0.99  inst_num_of_non_proper_insts:           1270
% 3.94/0.99  inst_num_of_duplicates:                 0
% 3.94/0.99  inst_inst_num_from_inst_to_res:         0
% 3.94/0.99  inst_dismatching_checking_time:         0.
% 3.94/0.99  
% 3.94/0.99  ------ Resolution
% 3.94/0.99  
% 3.94/0.99  res_num_of_clauses:                     0
% 3.94/0.99  res_num_in_passive:                     0
% 3.94/0.99  res_num_in_active:                      0
% 3.94/0.99  res_num_of_loops:                       157
% 3.94/0.99  res_forward_subset_subsumed:            43
% 3.94/0.99  res_backward_subset_subsumed:           4
% 3.94/0.99  res_forward_subsumed:                   0
% 3.94/0.99  res_backward_subsumed:                  1
% 3.94/0.99  res_forward_subsumption_resolution:     2
% 3.94/0.99  res_backward_subsumption_resolution:    0
% 3.94/0.99  res_clause_to_clause_subsumption:       1099
% 3.94/0.99  res_orphan_elimination:                 0
% 3.94/0.99  res_tautology_del:                      52
% 3.94/0.99  res_num_eq_res_simplified:              0
% 3.94/0.99  res_num_sel_changes:                    0
% 3.94/0.99  res_moves_from_active_to_pass:          0
% 3.94/0.99  
% 3.94/0.99  ------ Superposition
% 3.94/0.99  
% 3.94/0.99  sup_time_total:                         0.
% 3.94/0.99  sup_time_generating:                    0.
% 3.94/0.99  sup_time_sim_full:                      0.
% 3.94/0.99  sup_time_sim_immed:                     0.
% 3.94/0.99  
% 3.94/0.99  sup_num_of_clauses:                     365
% 3.94/0.99  sup_num_in_active:                      162
% 3.94/0.99  sup_num_in_passive:                     203
% 3.94/0.99  sup_num_of_loops:                       170
% 3.94/0.99  sup_fw_superposition:                   290
% 3.94/0.99  sup_bw_superposition:                   126
% 3.94/0.99  sup_immediate_simplified:               101
% 3.94/0.99  sup_given_eliminated:                   1
% 3.94/0.99  comparisons_done:                       0
% 3.94/0.99  comparisons_avoided:                    0
% 3.94/0.99  
% 3.94/0.99  ------ Simplifications
% 3.94/0.99  
% 3.94/0.99  
% 3.94/0.99  sim_fw_subset_subsumed:                 10
% 3.94/0.99  sim_bw_subset_subsumed:                 14
% 3.94/0.99  sim_fw_subsumed:                        17
% 3.94/0.99  sim_bw_subsumed:                        0
% 3.94/0.99  sim_fw_subsumption_res:                 12
% 3.94/0.99  sim_bw_subsumption_res:                 0
% 3.94/0.99  sim_tautology_del:                      0
% 3.94/0.99  sim_eq_tautology_del:                   15
% 3.94/0.99  sim_eq_res_simp:                        1
% 3.94/0.99  sim_fw_demodulated:                     9
% 3.94/0.99  sim_bw_demodulated:                     6
% 3.94/0.99  sim_light_normalised:                   84
% 3.94/0.99  sim_joinable_taut:                      0
% 3.94/0.99  sim_joinable_simp:                      0
% 3.94/0.99  sim_ac_normalised:                      0
% 3.94/0.99  sim_smt_subsumption:                    0
% 3.94/0.99  
%------------------------------------------------------------------------------
