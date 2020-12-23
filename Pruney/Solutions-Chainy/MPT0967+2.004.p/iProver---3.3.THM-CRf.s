%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:37 EST 2020

% Result     : Theorem 3.02s
% Output     : CNFRefutation 3.02s
% Verified   : 
% Statistics : Number of formulae       :  196 (2788 expanded)
%              Number of clauses        :  132 (1018 expanded)
%              Number of leaves         :   18 ( 484 expanded)
%              Depth                    :   24
%              Number of atoms          :  631 (15260 expanded)
%              Number of equality atoms :  299 (3946 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f50])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f97,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f62])).

fof(f18,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X1,X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X1,X2)
         => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_2(X3,X0,X2)
              & v1_funct_1(X3) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f42,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f43,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f42])).

fof(f54,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
          | ~ v1_funct_2(X3,X0,X2)
          | ~ v1_funct_1(X3) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
        | ~ v1_funct_2(sK5,sK2,sK4)
        | ~ v1_funct_1(sK5) )
      & ( k1_xboole_0 = sK2
        | k1_xboole_0 != sK3 )
      & r1_tarski(sK3,sK4)
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_2(sK5,sK2,sK3)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
      | ~ v1_funct_2(sK5,sK2,sK4)
      | ~ v1_funct_1(sK5) )
    & ( k1_xboole_0 = sK2
      | k1_xboole_0 != sK3 )
    & r1_tarski(sK3,sK4)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK5,sK2,sK3)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f43,f54])).

fof(f92,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f55])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f40])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f90,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f55])).

fof(f91,plain,(
    v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X2)
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f93,plain,(
    r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f55])).

fof(f95,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
    | ~ v1_funct_2(sK5,sK2,sK4)
    | ~ v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f55])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( ( r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f36])).

fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f94,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f55])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
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

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f39])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f103,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f79])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f102,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f81])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_tarski(k2_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f34])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f6,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f67,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f66,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f98,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f66])).

cnf(c_8,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1483,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1466,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_39,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_559,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
    | sK5 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_39])).

cnf(c_560,plain,
    ( ~ v1_funct_2(sK5,X0,X1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
    | ~ r1_tarski(k2_relset_1(X0,X1,sK5),X2)
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_559])).

cnf(c_1460,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(sK5,X1,X0) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k2_relset_1(X1,X0,sK5),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_560])).

cnf(c_1878,plain,
    ( sK3 = k1_xboole_0
    | v1_funct_2(sK5,sK2,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relset_1(sK2,sK3,sK5),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1466,c_1460])).

cnf(c_38,negated_conjecture,
    ( v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_41,plain,
    ( v1_funct_2(sK5,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_2199,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relset_1(sK2,sK3,sK5),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1878,c_41])).

cnf(c_2208,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relset_1(sK2,sK3,sK5)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1483,c_2199])).

cnf(c_2268,plain,
    ( k2_relset_1(sK2,sK3,sK5) = k1_xboole_0
    | sK3 = k1_xboole_0
    | v1_funct_2(sK5,sK2,k2_relset_1(sK2,sK3,sK5)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relset_1(sK2,k2_relset_1(sK2,sK3,sK5),sK5),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2208,c_1460])).

cnf(c_31,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X0,X1,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_524,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X0,X1,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
    | sK5 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_39])).

cnf(c_525,plain,
    ( ~ v1_funct_2(sK5,X0,X1)
    | v1_funct_2(sK5,X0,X2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r1_tarski(k2_relset_1(X0,X1,sK5),X2)
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_524])).

cnf(c_1462,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(sK5,X1,X0) != iProver_top
    | v1_funct_2(sK5,X1,X2) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
    | r1_tarski(k2_relset_1(X1,X0,sK5),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_525])).

cnf(c_1841,plain,
    ( sK3 = k1_xboole_0
    | v1_funct_2(sK5,sK2,X0) = iProver_top
    | v1_funct_2(sK5,sK2,sK3) != iProver_top
    | r1_tarski(k2_relset_1(sK2,sK3,sK5),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1466,c_1462])).

cnf(c_2085,plain,
    ( v1_funct_2(sK5,sK2,X0) = iProver_top
    | sK3 = k1_xboole_0
    | r1_tarski(k2_relset_1(sK2,sK3,sK5),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1841,c_41])).

cnf(c_2086,plain,
    ( sK3 = k1_xboole_0
    | v1_funct_2(sK5,sK2,X0) = iProver_top
    | r1_tarski(k2_relset_1(sK2,sK3,sK5),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2085])).

cnf(c_2094,plain,
    ( sK3 = k1_xboole_0
    | v1_funct_2(sK5,sK2,k2_relset_1(sK2,sK3,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1483,c_2086])).

cnf(c_2345,plain,
    ( sK3 = k1_xboole_0
    | k2_relset_1(sK2,sK3,sK5) = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relset_1(sK2,k2_relset_1(sK2,sK3,sK5),sK5),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2268,c_2094])).

cnf(c_2346,plain,
    ( k2_relset_1(sK2,sK3,sK5) = k1_xboole_0
    | sK3 = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relset_1(sK2,k2_relset_1(sK2,sK3,sK5),sK5),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2345])).

cnf(c_2355,plain,
    ( k2_relset_1(sK2,sK3,sK5) = k1_xboole_0
    | sK3 = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relset_1(sK2,k2_relset_1(sK2,sK3,sK5),sK5)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1483,c_2346])).

cnf(c_13,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v5_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_443,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X3),X4)
    | ~ v1_relat_1(X3)
    | X0 != X3
    | X2 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_16])).

cnf(c_444,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_443])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_448,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_444,c_15])).

cnf(c_449,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_448])).

cnf(c_1463,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_449])).

cnf(c_2482,plain,
    ( k2_relset_1(sK2,sK3,sK5) = k1_xboole_0
    | sK3 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK5),k2_relset_1(sK2,k2_relset_1(sK2,sK3,sK5),sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2355,c_1463])).

cnf(c_42,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_36,negated_conjecture,
    ( r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_43,plain,
    ( r1_tarski(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_34,negated_conjecture,
    ( ~ v1_funct_2(sK5,sK2,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
    | ~ v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_202,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
    | ~ v1_funct_2(sK5,sK2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_34,c_39])).

cnf(c_203,negated_conjecture,
    ( ~ v1_funct_2(sK5,sK2,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) ),
    inference(renaming,[status(thm)],[c_202])).

cnf(c_204,plain,
    ( v1_funct_2(sK5,sK2,sK4) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_203])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X2,X4) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1810,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ r1_tarski(sK3,X1)
    | ~ r1_tarski(sK2,X0) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1953,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ r1_tarski(sK3,sK4)
    | ~ r1_tarski(sK2,X0) ),
    inference(instantiation,[status(thm)],[c_1810])).

cnf(c_1998,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
    | ~ r1_tarski(sK3,sK4)
    | ~ r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_1953])).

cnf(c_2000,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) = iProver_top
    | r1_tarski(sK3,sK4) != iProver_top
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1998])).

cnf(c_1999,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2002,plain,
    ( r1_tarski(sK2,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1999])).

cnf(c_1467,plain,
    ( r1_tarski(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_1474,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) = iProver_top
    | r1_tarski(X1,X3) != iProver_top
    | r1_tarski(X2,X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_5066,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
    | r1_tarski(sK3,X1) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1466,c_1474])).

cnf(c_5102,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X3,X1) != iProver_top
    | r1_tarski(sK3,X3) != iProver_top
    | r1_tarski(sK2,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5066,c_1474])).

cnf(c_6301,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,sK4))) = iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(sK3,sK3) != iProver_top
    | r1_tarski(sK2,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1467,c_5102])).

cnf(c_1946,plain,
    ( r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1951,plain,
    ( r1_tarski(sK3,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1946])).

cnf(c_6346,plain,
    ( r1_tarski(X1,X0) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,sK4))) = iProver_top
    | r1_tarski(sK2,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6301,c_1951])).

cnf(c_6347,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,sK4))) = iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(sK2,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_6346])).

cnf(c_6356,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) = iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1467,c_6347])).

cnf(c_6522,plain,
    ( r1_tarski(k2_relat_1(sK5),sK4) = iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6356,c_1463])).

cnf(c_1758,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | r1_tarski(k2_relat_1(sK5),sK3) ),
    inference(instantiation,[status(thm)],[c_449])).

cnf(c_1759,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | r1_tarski(k2_relat_1(sK5),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1758])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1779,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(k2_relat_1(X2),X0)
    | r1_tarski(k2_relat_1(X2),X1) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1896,plain,
    ( r1_tarski(k2_relat_1(sK5),X0)
    | ~ r1_tarski(k2_relat_1(sK5),sK3)
    | ~ r1_tarski(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_1779])).

cnf(c_2132,plain,
    ( ~ r1_tarski(k2_relat_1(sK5),sK3)
    | r1_tarski(k2_relat_1(sK5),sK4)
    | ~ r1_tarski(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1896])).

cnf(c_2133,plain,
    ( r1_tarski(k2_relat_1(sK5),sK3) != iProver_top
    | r1_tarski(k2_relat_1(sK5),sK4) = iProver_top
    | r1_tarski(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2132])).

cnf(c_6606,plain,
    ( r1_tarski(k2_relat_1(sK5),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6522,c_42,c_43,c_1759,c_2133])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1476,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3436,plain,
    ( k2_relset_1(sK2,sK3,sK5) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1466,c_1476])).

cnf(c_3719,plain,
    ( sK3 = k1_xboole_0
    | v1_funct_2(sK5,sK2,X0) = iProver_top
    | r1_tarski(k2_relat_1(sK5),X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3436,c_2086])).

cnf(c_6615,plain,
    ( sK3 = k1_xboole_0
    | v1_funct_2(sK5,sK2,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_6606,c_3719])).

cnf(c_7015,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2482,c_42,c_43,c_204,c_2000,c_2002,c_6615])).

cnf(c_7032,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7015,c_1466])).

cnf(c_35,negated_conjecture,
    ( k1_xboole_0 != sK3
    | k1_xboole_0 = sK2 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_7035,plain,
    ( sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7015,c_35])).

cnf(c_7036,plain,
    ( sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_7035])).

cnf(c_7044,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7032,c_7036])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1469,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_8165,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_xboole_0
    | v1_funct_2(sK5,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7044,c_1469])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1477,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3484,plain,
    ( k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1466,c_1477])).

cnf(c_7029,plain,
    ( k1_relset_1(sK2,k1_xboole_0,sK5) = k1_relat_1(sK5) ),
    inference(demodulation,[status(thm)],[c_7015,c_3484])).

cnf(c_7052,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_relat_1(sK5) ),
    inference(light_normalisation,[status(thm)],[c_7029,c_7036])).

cnf(c_8183,plain,
    ( k1_relat_1(sK5) = k1_xboole_0
    | v1_funct_2(sK5,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8165,c_7052])).

cnf(c_5107,plain,
    ( k1_relset_1(X0,X1,sK5) = k1_relat_1(sK5)
    | r1_tarski(sK3,X1) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5066,c_1477])).

cnf(c_5377,plain,
    ( k1_relset_1(X0,sK4,sK5) = k1_relat_1(sK5)
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1467,c_5107])).

cnf(c_5395,plain,
    ( k1_relset_1(sK2,sK4,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1483,c_5377])).

cnf(c_7149,plain,
    ( k1_relset_1(k1_xboole_0,sK4,sK5) = k1_relat_1(sK5) ),
    inference(demodulation,[status(thm)],[c_7036,c_5395])).

cnf(c_24,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1471,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_7846,plain,
    ( k1_relat_1(sK5) != k1_xboole_0
    | v1_funct_2(sK5,k1_xboole_0,sK4) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7149,c_1471])).

cnf(c_3718,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK5),X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3436,c_2199])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ r1_tarski(k2_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2541,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
    | ~ r1_tarski(k2_relat_1(sK5),X2) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_3940,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
    | ~ r1_tarski(k2_relat_1(sK5),X0) ),
    inference(instantiation,[status(thm)],[c_2541])).

cnf(c_3941,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top
    | r1_tarski(k2_relat_1(sK5),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3940])).

cnf(c_4796,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK5),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3718,c_42,c_43,c_2000,c_2002,c_3941])).

cnf(c_1464,plain,
    ( v1_funct_2(sK5,sK2,sK4) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_203])).

cnf(c_4806,plain,
    ( v1_funct_2(sK5,sK2,sK4) != iProver_top
    | r1_tarski(k2_relat_1(sK5),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4796,c_1464])).

cnf(c_4863,plain,
    ( v1_funct_2(sK5,sK2,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4806,c_42,c_43,c_204,c_2000,c_2002])).

cnf(c_7151,plain,
    ( v1_funct_2(sK5,k1_xboole_0,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7036,c_4863])).

cnf(c_892,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2004,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,X2)
    | X2 != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_892])).

cnf(c_2908,plain,
    ( ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,X1)
    | X1 != X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2004])).

cnf(c_5856,plain,
    ( r1_tarski(sK2,X0)
    | ~ r1_tarski(sK2,sK2)
    | X0 != sK2
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2908])).

cnf(c_5857,plain,
    ( X0 != sK2
    | sK2 != sK2
    | r1_tarski(sK2,X0) = iProver_top
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5856])).

cnf(c_5859,plain,
    ( sK2 != sK2
    | k1_xboole_0 != sK2
    | r1_tarski(sK2,sK2) != iProver_top
    | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5857])).

cnf(c_3873,plain,
    ( r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_3878,plain,
    ( r1_tarski(sK4,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3873])).

cnf(c_2387,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
    | ~ r1_tarski(sK4,X1)
    | ~ r1_tarski(sK2,X0) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_3872,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
    | ~ r1_tarski(sK4,sK4)
    | ~ r1_tarski(sK2,X0) ),
    inference(instantiation,[status(thm)],[c_2387])).

cnf(c_3874,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,sK4))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top
    | r1_tarski(sK4,sK4) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3872])).

cnf(c_3876,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4))) = iProver_top
    | r1_tarski(sK4,sK4) != iProver_top
    | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3874])).

cnf(c_887,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2909,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_887])).

cnf(c_898,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_1825,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(sK5,sK2,sK3)
    | X2 != sK3
    | X1 != sK2
    | X0 != sK5 ),
    inference(instantiation,[status(thm)],[c_898])).

cnf(c_2374,plain,
    ( ~ v1_funct_2(sK5,sK2,sK3)
    | v1_funct_2(sK5,k1_xboole_0,X0)
    | X0 != sK3
    | sK5 != sK5
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_1825])).

cnf(c_2375,plain,
    ( X0 != sK3
    | sK5 != sK5
    | k1_xboole_0 != sK2
    | v1_funct_2(sK5,sK2,sK3) != iProver_top
    | v1_funct_2(sK5,k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2374])).

cnf(c_2377,plain,
    ( sK5 != sK5
    | k1_xboole_0 != sK3
    | k1_xboole_0 != sK2
    | v1_funct_2(sK5,sK2,sK3) != iProver_top
    | v1_funct_2(sK5,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2375])).

cnf(c_1937,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_887])).

cnf(c_888,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1771,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_888])).

cnf(c_1772,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1771])).

cnf(c_10,plain,
    ( ~ r1_xboole_0(X0,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_95,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_11,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f98])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8183,c_7846,c_7151,c_6615,c_5859,c_3878,c_3876,c_2909,c_2377,c_2002,c_2000,c_1937,c_1772,c_204,c_95,c_11,c_35,c_43,c_42,c_41])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:53:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.02/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.02/0.99  
% 3.02/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.02/0.99  
% 3.02/0.99  ------  iProver source info
% 3.02/0.99  
% 3.02/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.02/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.02/0.99  git: non_committed_changes: false
% 3.02/0.99  git: last_make_outside_of_git: false
% 3.02/0.99  
% 3.02/0.99  ------ 
% 3.02/0.99  
% 3.02/0.99  ------ Input Options
% 3.02/0.99  
% 3.02/0.99  --out_options                           all
% 3.02/0.99  --tptp_safe_out                         true
% 3.02/0.99  --problem_path                          ""
% 3.02/0.99  --include_path                          ""
% 3.02/0.99  --clausifier                            res/vclausify_rel
% 3.02/0.99  --clausifier_options                    --mode clausify
% 3.02/0.99  --stdin                                 false
% 3.02/0.99  --stats_out                             all
% 3.02/0.99  
% 3.02/0.99  ------ General Options
% 3.02/0.99  
% 3.02/0.99  --fof                                   false
% 3.02/0.99  --time_out_real                         305.
% 3.02/0.99  --time_out_virtual                      -1.
% 3.02/0.99  --symbol_type_check                     false
% 3.02/0.99  --clausify_out                          false
% 3.02/0.99  --sig_cnt_out                           false
% 3.02/0.99  --trig_cnt_out                          false
% 3.02/0.99  --trig_cnt_out_tolerance                1.
% 3.02/0.99  --trig_cnt_out_sk_spl                   false
% 3.02/0.99  --abstr_cl_out                          false
% 3.02/0.99  
% 3.02/0.99  ------ Global Options
% 3.02/0.99  
% 3.02/0.99  --schedule                              default
% 3.02/0.99  --add_important_lit                     false
% 3.02/0.99  --prop_solver_per_cl                    1000
% 3.02/0.99  --min_unsat_core                        false
% 3.02/0.99  --soft_assumptions                      false
% 3.02/0.99  --soft_lemma_size                       3
% 3.02/0.99  --prop_impl_unit_size                   0
% 3.02/0.99  --prop_impl_unit                        []
% 3.02/0.99  --share_sel_clauses                     true
% 3.02/0.99  --reset_solvers                         false
% 3.02/0.99  --bc_imp_inh                            [conj_cone]
% 3.02/0.99  --conj_cone_tolerance                   3.
% 3.02/0.99  --extra_neg_conj                        none
% 3.02/0.99  --large_theory_mode                     true
% 3.02/0.99  --prolific_symb_bound                   200
% 3.02/0.99  --lt_threshold                          2000
% 3.02/0.99  --clause_weak_htbl                      true
% 3.02/0.99  --gc_record_bc_elim                     false
% 3.02/0.99  
% 3.02/0.99  ------ Preprocessing Options
% 3.02/0.99  
% 3.02/0.99  --preprocessing_flag                    true
% 3.02/0.99  --time_out_prep_mult                    0.1
% 3.02/0.99  --splitting_mode                        input
% 3.02/0.99  --splitting_grd                         true
% 3.02/0.99  --splitting_cvd                         false
% 3.02/0.99  --splitting_cvd_svl                     false
% 3.02/0.99  --splitting_nvd                         32
% 3.02/0.99  --sub_typing                            true
% 3.02/0.99  --prep_gs_sim                           true
% 3.02/0.99  --prep_unflatten                        true
% 3.02/0.99  --prep_res_sim                          true
% 3.02/0.99  --prep_upred                            true
% 3.02/0.99  --prep_sem_filter                       exhaustive
% 3.02/0.99  --prep_sem_filter_out                   false
% 3.02/0.99  --pred_elim                             true
% 3.02/0.99  --res_sim_input                         true
% 3.02/0.99  --eq_ax_congr_red                       true
% 3.02/0.99  --pure_diseq_elim                       true
% 3.02/0.99  --brand_transform                       false
% 3.02/0.99  --non_eq_to_eq                          false
% 3.02/0.99  --prep_def_merge                        true
% 3.02/0.99  --prep_def_merge_prop_impl              false
% 3.02/0.99  --prep_def_merge_mbd                    true
% 3.02/0.99  --prep_def_merge_tr_red                 false
% 3.02/0.99  --prep_def_merge_tr_cl                  false
% 3.02/0.99  --smt_preprocessing                     true
% 3.02/0.99  --smt_ac_axioms                         fast
% 3.02/0.99  --preprocessed_out                      false
% 3.02/0.99  --preprocessed_stats                    false
% 3.02/0.99  
% 3.02/0.99  ------ Abstraction refinement Options
% 3.02/0.99  
% 3.02/0.99  --abstr_ref                             []
% 3.02/0.99  --abstr_ref_prep                        false
% 3.02/0.99  --abstr_ref_until_sat                   false
% 3.02/0.99  --abstr_ref_sig_restrict                funpre
% 3.02/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.02/0.99  --abstr_ref_under                       []
% 3.02/0.99  
% 3.02/0.99  ------ SAT Options
% 3.02/0.99  
% 3.02/0.99  --sat_mode                              false
% 3.02/0.99  --sat_fm_restart_options                ""
% 3.02/0.99  --sat_gr_def                            false
% 3.02/0.99  --sat_epr_types                         true
% 3.02/0.99  --sat_non_cyclic_types                  false
% 3.02/0.99  --sat_finite_models                     false
% 3.02/0.99  --sat_fm_lemmas                         false
% 3.02/0.99  --sat_fm_prep                           false
% 3.02/0.99  --sat_fm_uc_incr                        true
% 3.02/0.99  --sat_out_model                         small
% 3.02/0.99  --sat_out_clauses                       false
% 3.02/0.99  
% 3.02/0.99  ------ QBF Options
% 3.02/0.99  
% 3.02/0.99  --qbf_mode                              false
% 3.02/0.99  --qbf_elim_univ                         false
% 3.02/0.99  --qbf_dom_inst                          none
% 3.02/0.99  --qbf_dom_pre_inst                      false
% 3.02/0.99  --qbf_sk_in                             false
% 3.02/0.99  --qbf_pred_elim                         true
% 3.02/0.99  --qbf_split                             512
% 3.02/0.99  
% 3.02/0.99  ------ BMC1 Options
% 3.02/0.99  
% 3.02/0.99  --bmc1_incremental                      false
% 3.02/0.99  --bmc1_axioms                           reachable_all
% 3.02/0.99  --bmc1_min_bound                        0
% 3.02/0.99  --bmc1_max_bound                        -1
% 3.02/0.99  --bmc1_max_bound_default                -1
% 3.02/0.99  --bmc1_symbol_reachability              true
% 3.02/0.99  --bmc1_property_lemmas                  false
% 3.02/0.99  --bmc1_k_induction                      false
% 3.02/0.99  --bmc1_non_equiv_states                 false
% 3.02/0.99  --bmc1_deadlock                         false
% 3.02/0.99  --bmc1_ucm                              false
% 3.02/0.99  --bmc1_add_unsat_core                   none
% 3.02/0.99  --bmc1_unsat_core_children              false
% 3.02/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.02/0.99  --bmc1_out_stat                         full
% 3.02/0.99  --bmc1_ground_init                      false
% 3.02/0.99  --bmc1_pre_inst_next_state              false
% 3.02/0.99  --bmc1_pre_inst_state                   false
% 3.02/0.99  --bmc1_pre_inst_reach_state             false
% 3.02/0.99  --bmc1_out_unsat_core                   false
% 3.02/0.99  --bmc1_aig_witness_out                  false
% 3.02/0.99  --bmc1_verbose                          false
% 3.02/0.99  --bmc1_dump_clauses_tptp                false
% 3.02/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.02/0.99  --bmc1_dump_file                        -
% 3.02/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.02/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.02/0.99  --bmc1_ucm_extend_mode                  1
% 3.02/0.99  --bmc1_ucm_init_mode                    2
% 3.02/0.99  --bmc1_ucm_cone_mode                    none
% 3.02/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.02/0.99  --bmc1_ucm_relax_model                  4
% 3.02/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.02/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.02/0.99  --bmc1_ucm_layered_model                none
% 3.02/0.99  --bmc1_ucm_max_lemma_size               10
% 3.02/0.99  
% 3.02/0.99  ------ AIG Options
% 3.02/0.99  
% 3.02/0.99  --aig_mode                              false
% 3.02/0.99  
% 3.02/0.99  ------ Instantiation Options
% 3.02/0.99  
% 3.02/0.99  --instantiation_flag                    true
% 3.02/0.99  --inst_sos_flag                         false
% 3.02/0.99  --inst_sos_phase                        true
% 3.02/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.02/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.02/0.99  --inst_lit_sel_side                     num_symb
% 3.02/0.99  --inst_solver_per_active                1400
% 3.02/0.99  --inst_solver_calls_frac                1.
% 3.02/0.99  --inst_passive_queue_type               priority_queues
% 3.02/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.02/0.99  --inst_passive_queues_freq              [25;2]
% 3.02/0.99  --inst_dismatching                      true
% 3.02/0.99  --inst_eager_unprocessed_to_passive     true
% 3.02/0.99  --inst_prop_sim_given                   true
% 3.02/0.99  --inst_prop_sim_new                     false
% 3.02/0.99  --inst_subs_new                         false
% 3.02/0.99  --inst_eq_res_simp                      false
% 3.02/0.99  --inst_subs_given                       false
% 3.02/0.99  --inst_orphan_elimination               true
% 3.02/0.99  --inst_learning_loop_flag               true
% 3.02/0.99  --inst_learning_start                   3000
% 3.02/0.99  --inst_learning_factor                  2
% 3.02/0.99  --inst_start_prop_sim_after_learn       3
% 3.02/0.99  --inst_sel_renew                        solver
% 3.02/0.99  --inst_lit_activity_flag                true
% 3.02/0.99  --inst_restr_to_given                   false
% 3.02/0.99  --inst_activity_threshold               500
% 3.02/0.99  --inst_out_proof                        true
% 3.02/0.99  
% 3.02/0.99  ------ Resolution Options
% 3.02/0.99  
% 3.02/0.99  --resolution_flag                       true
% 3.02/0.99  --res_lit_sel                           adaptive
% 3.02/0.99  --res_lit_sel_side                      none
% 3.02/0.99  --res_ordering                          kbo
% 3.02/0.99  --res_to_prop_solver                    active
% 3.02/0.99  --res_prop_simpl_new                    false
% 3.02/0.99  --res_prop_simpl_given                  true
% 3.02/0.99  --res_passive_queue_type                priority_queues
% 3.02/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.02/0.99  --res_passive_queues_freq               [15;5]
% 3.02/0.99  --res_forward_subs                      full
% 3.02/0.99  --res_backward_subs                     full
% 3.02/0.99  --res_forward_subs_resolution           true
% 3.02/0.99  --res_backward_subs_resolution          true
% 3.02/0.99  --res_orphan_elimination                true
% 3.02/0.99  --res_time_limit                        2.
% 3.02/0.99  --res_out_proof                         true
% 3.02/0.99  
% 3.02/0.99  ------ Superposition Options
% 3.02/0.99  
% 3.02/0.99  --superposition_flag                    true
% 3.02/0.99  --sup_passive_queue_type                priority_queues
% 3.02/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.02/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.02/0.99  --demod_completeness_check              fast
% 3.02/0.99  --demod_use_ground                      true
% 3.02/0.99  --sup_to_prop_solver                    passive
% 3.02/0.99  --sup_prop_simpl_new                    true
% 3.02/0.99  --sup_prop_simpl_given                  true
% 3.02/0.99  --sup_fun_splitting                     false
% 3.02/0.99  --sup_smt_interval                      50000
% 3.02/0.99  
% 3.02/0.99  ------ Superposition Simplification Setup
% 3.02/0.99  
% 3.02/0.99  --sup_indices_passive                   []
% 3.02/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.02/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/0.99  --sup_full_bw                           [BwDemod]
% 3.02/0.99  --sup_immed_triv                        [TrivRules]
% 3.02/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.02/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/0.99  --sup_immed_bw_main                     []
% 3.02/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.02/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.02/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.02/0.99  
% 3.02/0.99  ------ Combination Options
% 3.02/0.99  
% 3.02/0.99  --comb_res_mult                         3
% 3.02/0.99  --comb_sup_mult                         2
% 3.02/0.99  --comb_inst_mult                        10
% 3.02/0.99  
% 3.02/0.99  ------ Debug Options
% 3.02/0.99  
% 3.02/0.99  --dbg_backtrace                         false
% 3.02/0.99  --dbg_dump_prop_clauses                 false
% 3.02/0.99  --dbg_dump_prop_clauses_file            -
% 3.02/0.99  --dbg_out_stat                          false
% 3.02/0.99  ------ Parsing...
% 3.02/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.02/0.99  
% 3.02/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.02/0.99  
% 3.02/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.02/0.99  
% 3.02/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.02/0.99  ------ Proving...
% 3.02/0.99  ------ Problem Properties 
% 3.02/0.99  
% 3.02/0.99  
% 3.02/0.99  clauses                                 33
% 3.02/0.99  conjectures                             5
% 3.02/0.99  EPR                                     11
% 3.02/0.99  Horn                                    24
% 3.02/0.99  unary                                   5
% 3.02/0.99  binary                                  12
% 3.02/0.99  lits                                    87
% 3.02/0.99  lits eq                                 18
% 3.02/0.99  fd_pure                                 0
% 3.02/0.99  fd_pseudo                               0
% 3.02/0.99  fd_cond                                 7
% 3.02/0.99  fd_pseudo_cond                          1
% 3.02/0.99  AC symbols                              0
% 3.02/0.99  
% 3.02/0.99  ------ Schedule dynamic 5 is on 
% 3.02/0.99  
% 3.02/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.02/0.99  
% 3.02/0.99  
% 3.02/0.99  ------ 
% 3.02/0.99  Current options:
% 3.02/0.99  ------ 
% 3.02/0.99  
% 3.02/0.99  ------ Input Options
% 3.02/0.99  
% 3.02/0.99  --out_options                           all
% 3.02/0.99  --tptp_safe_out                         true
% 3.02/0.99  --problem_path                          ""
% 3.02/0.99  --include_path                          ""
% 3.02/0.99  --clausifier                            res/vclausify_rel
% 3.02/0.99  --clausifier_options                    --mode clausify
% 3.02/0.99  --stdin                                 false
% 3.02/0.99  --stats_out                             all
% 3.02/0.99  
% 3.02/0.99  ------ General Options
% 3.02/0.99  
% 3.02/0.99  --fof                                   false
% 3.02/0.99  --time_out_real                         305.
% 3.02/0.99  --time_out_virtual                      -1.
% 3.02/0.99  --symbol_type_check                     false
% 3.02/0.99  --clausify_out                          false
% 3.02/0.99  --sig_cnt_out                           false
% 3.02/0.99  --trig_cnt_out                          false
% 3.02/0.99  --trig_cnt_out_tolerance                1.
% 3.02/0.99  --trig_cnt_out_sk_spl                   false
% 3.02/0.99  --abstr_cl_out                          false
% 3.02/0.99  
% 3.02/0.99  ------ Global Options
% 3.02/0.99  
% 3.02/0.99  --schedule                              default
% 3.02/0.99  --add_important_lit                     false
% 3.02/0.99  --prop_solver_per_cl                    1000
% 3.02/0.99  --min_unsat_core                        false
% 3.02/0.99  --soft_assumptions                      false
% 3.02/0.99  --soft_lemma_size                       3
% 3.02/0.99  --prop_impl_unit_size                   0
% 3.02/0.99  --prop_impl_unit                        []
% 3.02/0.99  --share_sel_clauses                     true
% 3.02/0.99  --reset_solvers                         false
% 3.02/0.99  --bc_imp_inh                            [conj_cone]
% 3.02/0.99  --conj_cone_tolerance                   3.
% 3.02/0.99  --extra_neg_conj                        none
% 3.02/0.99  --large_theory_mode                     true
% 3.02/0.99  --prolific_symb_bound                   200
% 3.02/0.99  --lt_threshold                          2000
% 3.02/0.99  --clause_weak_htbl                      true
% 3.02/0.99  --gc_record_bc_elim                     false
% 3.02/0.99  
% 3.02/0.99  ------ Preprocessing Options
% 3.02/0.99  
% 3.02/0.99  --preprocessing_flag                    true
% 3.02/0.99  --time_out_prep_mult                    0.1
% 3.02/0.99  --splitting_mode                        input
% 3.02/0.99  --splitting_grd                         true
% 3.02/0.99  --splitting_cvd                         false
% 3.02/0.99  --splitting_cvd_svl                     false
% 3.02/0.99  --splitting_nvd                         32
% 3.02/0.99  --sub_typing                            true
% 3.02/0.99  --prep_gs_sim                           true
% 3.02/0.99  --prep_unflatten                        true
% 3.02/0.99  --prep_res_sim                          true
% 3.02/0.99  --prep_upred                            true
% 3.02/0.99  --prep_sem_filter                       exhaustive
% 3.02/0.99  --prep_sem_filter_out                   false
% 3.02/0.99  --pred_elim                             true
% 3.02/0.99  --res_sim_input                         true
% 3.02/0.99  --eq_ax_congr_red                       true
% 3.02/0.99  --pure_diseq_elim                       true
% 3.02/0.99  --brand_transform                       false
% 3.02/0.99  --non_eq_to_eq                          false
% 3.02/0.99  --prep_def_merge                        true
% 3.02/0.99  --prep_def_merge_prop_impl              false
% 3.02/0.99  --prep_def_merge_mbd                    true
% 3.02/0.99  --prep_def_merge_tr_red                 false
% 3.02/0.99  --prep_def_merge_tr_cl                  false
% 3.02/0.99  --smt_preprocessing                     true
% 3.02/0.99  --smt_ac_axioms                         fast
% 3.02/0.99  --preprocessed_out                      false
% 3.02/0.99  --preprocessed_stats                    false
% 3.02/0.99  
% 3.02/0.99  ------ Abstraction refinement Options
% 3.02/0.99  
% 3.02/0.99  --abstr_ref                             []
% 3.02/0.99  --abstr_ref_prep                        false
% 3.02/0.99  --abstr_ref_until_sat                   false
% 3.02/0.99  --abstr_ref_sig_restrict                funpre
% 3.02/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.02/0.99  --abstr_ref_under                       []
% 3.02/0.99  
% 3.02/0.99  ------ SAT Options
% 3.02/0.99  
% 3.02/0.99  --sat_mode                              false
% 3.02/0.99  --sat_fm_restart_options                ""
% 3.02/0.99  --sat_gr_def                            false
% 3.02/0.99  --sat_epr_types                         true
% 3.02/0.99  --sat_non_cyclic_types                  false
% 3.02/0.99  --sat_finite_models                     false
% 3.02/0.99  --sat_fm_lemmas                         false
% 3.02/0.99  --sat_fm_prep                           false
% 3.02/0.99  --sat_fm_uc_incr                        true
% 3.02/0.99  --sat_out_model                         small
% 3.02/0.99  --sat_out_clauses                       false
% 3.02/0.99  
% 3.02/0.99  ------ QBF Options
% 3.02/0.99  
% 3.02/0.99  --qbf_mode                              false
% 3.02/0.99  --qbf_elim_univ                         false
% 3.02/0.99  --qbf_dom_inst                          none
% 3.02/0.99  --qbf_dom_pre_inst                      false
% 3.02/0.99  --qbf_sk_in                             false
% 3.02/0.99  --qbf_pred_elim                         true
% 3.02/0.99  --qbf_split                             512
% 3.02/0.99  
% 3.02/0.99  ------ BMC1 Options
% 3.02/0.99  
% 3.02/0.99  --bmc1_incremental                      false
% 3.02/0.99  --bmc1_axioms                           reachable_all
% 3.02/0.99  --bmc1_min_bound                        0
% 3.02/0.99  --bmc1_max_bound                        -1
% 3.02/0.99  --bmc1_max_bound_default                -1
% 3.02/0.99  --bmc1_symbol_reachability              true
% 3.02/0.99  --bmc1_property_lemmas                  false
% 3.02/0.99  --bmc1_k_induction                      false
% 3.02/0.99  --bmc1_non_equiv_states                 false
% 3.02/0.99  --bmc1_deadlock                         false
% 3.02/0.99  --bmc1_ucm                              false
% 3.02/0.99  --bmc1_add_unsat_core                   none
% 3.02/0.99  --bmc1_unsat_core_children              false
% 3.02/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.02/0.99  --bmc1_out_stat                         full
% 3.02/0.99  --bmc1_ground_init                      false
% 3.02/0.99  --bmc1_pre_inst_next_state              false
% 3.02/0.99  --bmc1_pre_inst_state                   false
% 3.02/0.99  --bmc1_pre_inst_reach_state             false
% 3.02/0.99  --bmc1_out_unsat_core                   false
% 3.02/0.99  --bmc1_aig_witness_out                  false
% 3.02/0.99  --bmc1_verbose                          false
% 3.02/0.99  --bmc1_dump_clauses_tptp                false
% 3.02/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.02/0.99  --bmc1_dump_file                        -
% 3.02/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.02/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.02/0.99  --bmc1_ucm_extend_mode                  1
% 3.02/0.99  --bmc1_ucm_init_mode                    2
% 3.02/0.99  --bmc1_ucm_cone_mode                    none
% 3.02/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.02/0.99  --bmc1_ucm_relax_model                  4
% 3.02/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.02/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.02/0.99  --bmc1_ucm_layered_model                none
% 3.02/0.99  --bmc1_ucm_max_lemma_size               10
% 3.02/0.99  
% 3.02/0.99  ------ AIG Options
% 3.02/0.99  
% 3.02/0.99  --aig_mode                              false
% 3.02/0.99  
% 3.02/0.99  ------ Instantiation Options
% 3.02/0.99  
% 3.02/0.99  --instantiation_flag                    true
% 3.02/0.99  --inst_sos_flag                         false
% 3.02/0.99  --inst_sos_phase                        true
% 3.02/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.02/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.02/0.99  --inst_lit_sel_side                     none
% 3.02/0.99  --inst_solver_per_active                1400
% 3.02/0.99  --inst_solver_calls_frac                1.
% 3.02/0.99  --inst_passive_queue_type               priority_queues
% 3.02/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.02/0.99  --inst_passive_queues_freq              [25;2]
% 3.02/0.99  --inst_dismatching                      true
% 3.02/0.99  --inst_eager_unprocessed_to_passive     true
% 3.02/0.99  --inst_prop_sim_given                   true
% 3.02/0.99  --inst_prop_sim_new                     false
% 3.02/0.99  --inst_subs_new                         false
% 3.02/0.99  --inst_eq_res_simp                      false
% 3.02/0.99  --inst_subs_given                       false
% 3.02/0.99  --inst_orphan_elimination               true
% 3.02/0.99  --inst_learning_loop_flag               true
% 3.02/0.99  --inst_learning_start                   3000
% 3.02/0.99  --inst_learning_factor                  2
% 3.02/0.99  --inst_start_prop_sim_after_learn       3
% 3.02/0.99  --inst_sel_renew                        solver
% 3.02/0.99  --inst_lit_activity_flag                true
% 3.02/0.99  --inst_restr_to_given                   false
% 3.02/0.99  --inst_activity_threshold               500
% 3.02/0.99  --inst_out_proof                        true
% 3.02/0.99  
% 3.02/0.99  ------ Resolution Options
% 3.02/0.99  
% 3.02/0.99  --resolution_flag                       false
% 3.02/0.99  --res_lit_sel                           adaptive
% 3.02/0.99  --res_lit_sel_side                      none
% 3.02/0.99  --res_ordering                          kbo
% 3.02/0.99  --res_to_prop_solver                    active
% 3.02/0.99  --res_prop_simpl_new                    false
% 3.02/0.99  --res_prop_simpl_given                  true
% 3.02/0.99  --res_passive_queue_type                priority_queues
% 3.02/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.02/0.99  --res_passive_queues_freq               [15;5]
% 3.02/0.99  --res_forward_subs                      full
% 3.02/0.99  --res_backward_subs                     full
% 3.02/0.99  --res_forward_subs_resolution           true
% 3.02/0.99  --res_backward_subs_resolution          true
% 3.02/0.99  --res_orphan_elimination                true
% 3.02/0.99  --res_time_limit                        2.
% 3.02/0.99  --res_out_proof                         true
% 3.02/0.99  
% 3.02/0.99  ------ Superposition Options
% 3.02/0.99  
% 3.02/0.99  --superposition_flag                    true
% 3.02/0.99  --sup_passive_queue_type                priority_queues
% 3.02/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.02/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.02/0.99  --demod_completeness_check              fast
% 3.02/0.99  --demod_use_ground                      true
% 3.02/0.99  --sup_to_prop_solver                    passive
% 3.02/0.99  --sup_prop_simpl_new                    true
% 3.02/0.99  --sup_prop_simpl_given                  true
% 3.02/0.99  --sup_fun_splitting                     false
% 3.02/0.99  --sup_smt_interval                      50000
% 3.02/0.99  
% 3.02/0.99  ------ Superposition Simplification Setup
% 3.02/0.99  
% 3.02/0.99  --sup_indices_passive                   []
% 3.02/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.02/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/0.99  --sup_full_bw                           [BwDemod]
% 3.02/0.99  --sup_immed_triv                        [TrivRules]
% 3.02/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.02/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/0.99  --sup_immed_bw_main                     []
% 3.02/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.02/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.02/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.02/0.99  
% 3.02/0.99  ------ Combination Options
% 3.02/0.99  
% 3.02/0.99  --comb_res_mult                         3
% 3.02/0.99  --comb_sup_mult                         2
% 3.02/0.99  --comb_inst_mult                        10
% 3.02/0.99  
% 3.02/0.99  ------ Debug Options
% 3.02/0.99  
% 3.02/0.99  --dbg_backtrace                         false
% 3.02/0.99  --dbg_dump_prop_clauses                 false
% 3.02/0.99  --dbg_dump_prop_clauses_file            -
% 3.02/0.99  --dbg_out_stat                          false
% 3.02/0.99  
% 3.02/0.99  
% 3.02/0.99  
% 3.02/0.99  
% 3.02/0.99  ------ Proving...
% 3.02/0.99  
% 3.02/0.99  
% 3.02/0.99  % SZS status Theorem for theBenchmark.p
% 3.02/0.99  
% 3.02/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.02/0.99  
% 3.02/0.99  fof(f4,axiom,(
% 3.02/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/0.99  
% 3.02/0.99  fof(f50,plain,(
% 3.02/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.02/0.99    inference(nnf_transformation,[],[f4])).
% 3.02/0.99  
% 3.02/0.99  fof(f51,plain,(
% 3.02/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.02/0.99    inference(flattening,[],[f50])).
% 3.02/0.99  
% 3.02/0.99  fof(f62,plain,(
% 3.02/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.02/0.99    inference(cnf_transformation,[],[f51])).
% 3.02/0.99  
% 3.02/0.99  fof(f97,plain,(
% 3.02/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.02/0.99    inference(equality_resolution,[],[f62])).
% 3.02/0.99  
% 3.02/0.99  fof(f18,conjecture,(
% 3.02/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/0.99  
% 3.02/0.99  fof(f19,negated_conjecture,(
% 3.02/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.02/0.99    inference(negated_conjecture,[],[f18])).
% 3.02/0.99  
% 3.02/0.99  fof(f42,plain,(
% 3.02/0.99    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X1,X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.02/0.99    inference(ennf_transformation,[],[f19])).
% 3.02/0.99  
% 3.02/0.99  fof(f43,plain,(
% 3.02/0.99    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.02/0.99    inference(flattening,[],[f42])).
% 3.02/0.99  
% 3.02/0.99  fof(f54,plain,(
% 3.02/0.99    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) | ~v1_funct_2(sK5,sK2,sK4) | ~v1_funct_1(sK5)) & (k1_xboole_0 = sK2 | k1_xboole_0 != sK3) & r1_tarski(sK3,sK4) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK5,sK2,sK3) & v1_funct_1(sK5))),
% 3.02/0.99    introduced(choice_axiom,[])).
% 3.02/0.99  
% 3.02/0.99  fof(f55,plain,(
% 3.02/0.99    (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) | ~v1_funct_2(sK5,sK2,sK4) | ~v1_funct_1(sK5)) & (k1_xboole_0 = sK2 | k1_xboole_0 != sK3) & r1_tarski(sK3,sK4) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK5,sK2,sK3) & v1_funct_1(sK5)),
% 3.02/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f43,f54])).
% 3.02/0.99  
% 3.02/0.99  fof(f92,plain,(
% 3.02/0.99    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 3.02/0.99    inference(cnf_transformation,[],[f55])).
% 3.02/0.99  
% 3.02/0.99  fof(f17,axiom,(
% 3.02/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/0.99  
% 3.02/0.99  fof(f40,plain,(
% 3.02/0.99    ! [X0,X1,X2,X3] : ((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.02/0.99    inference(ennf_transformation,[],[f17])).
% 3.02/0.99  
% 3.02/0.99  fof(f41,plain,(
% 3.02/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.02/0.99    inference(flattening,[],[f40])).
% 3.02/0.99  
% 3.02/0.99  fof(f88,plain,(
% 3.02/0.99    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.02/0.99    inference(cnf_transformation,[],[f41])).
% 3.02/0.99  
% 3.02/0.99  fof(f90,plain,(
% 3.02/0.99    v1_funct_1(sK5)),
% 3.02/0.99    inference(cnf_transformation,[],[f55])).
% 3.02/0.99  
% 3.02/0.99  fof(f91,plain,(
% 3.02/0.99    v1_funct_2(sK5,sK2,sK3)),
% 3.02/0.99    inference(cnf_transformation,[],[f55])).
% 3.02/0.99  
% 3.02/0.99  fof(f86,plain,(
% 3.02/0.99    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X2) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.02/0.99    inference(cnf_transformation,[],[f41])).
% 3.02/0.99  
% 3.02/0.99  fof(f7,axiom,(
% 3.02/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/0.99  
% 3.02/0.99  fof(f27,plain,(
% 3.02/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.02/0.99    inference(ennf_transformation,[],[f7])).
% 3.02/0.99  
% 3.02/0.99  fof(f52,plain,(
% 3.02/0.99    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.02/0.99    inference(nnf_transformation,[],[f27])).
% 3.02/0.99  
% 3.02/0.99  fof(f68,plain,(
% 3.02/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.02/0.99    inference(cnf_transformation,[],[f52])).
% 3.02/0.99  
% 3.02/0.99  fof(f10,axiom,(
% 3.02/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/0.99  
% 3.02/0.99  fof(f21,plain,(
% 3.02/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.02/0.99    inference(pure_predicate_removal,[],[f10])).
% 3.02/0.99  
% 3.02/0.99  fof(f30,plain,(
% 3.02/0.99    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.02/0.99    inference(ennf_transformation,[],[f21])).
% 3.02/0.99  
% 3.02/0.99  fof(f72,plain,(
% 3.02/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.02/0.99    inference(cnf_transformation,[],[f30])).
% 3.02/0.99  
% 3.02/0.99  fof(f9,axiom,(
% 3.02/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/0.99  
% 3.02/0.99  fof(f29,plain,(
% 3.02/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.02/0.99    inference(ennf_transformation,[],[f9])).
% 3.02/0.99  
% 3.02/0.99  fof(f71,plain,(
% 3.02/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.02/0.99    inference(cnf_transformation,[],[f29])).
% 3.02/0.99  
% 3.02/0.99  fof(f93,plain,(
% 3.02/0.99    r1_tarski(sK3,sK4)),
% 3.02/0.99    inference(cnf_transformation,[],[f55])).
% 3.02/0.99  
% 3.02/0.99  fof(f95,plain,(
% 3.02/0.99    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) | ~v1_funct_2(sK5,sK2,sK4) | ~v1_funct_1(sK5)),
% 3.02/0.99    inference(cnf_transformation,[],[f55])).
% 3.02/0.99  
% 3.02/0.99  fof(f15,axiom,(
% 3.02/0.99    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))))),
% 3.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/0.99  
% 3.02/0.99  fof(f36,plain,(
% 3.02/0.99    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 3.02/0.99    inference(ennf_transformation,[],[f15])).
% 3.02/0.99  
% 3.02/0.99  fof(f37,plain,(
% 3.02/0.99    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 3.02/0.99    inference(flattening,[],[f36])).
% 3.02/0.99  
% 3.02/0.99  fof(f77,plain,(
% 3.02/0.99    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 3.02/0.99    inference(cnf_transformation,[],[f37])).
% 3.02/0.99  
% 3.02/0.99  fof(f5,axiom,(
% 3.02/0.99    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/0.99  
% 3.02/0.99  fof(f24,plain,(
% 3.02/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.02/0.99    inference(ennf_transformation,[],[f5])).
% 3.02/0.99  
% 3.02/0.99  fof(f25,plain,(
% 3.02/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.02/0.99    inference(flattening,[],[f24])).
% 3.02/0.99  
% 3.02/0.99  fof(f65,plain,(
% 3.02/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.02/0.99    inference(cnf_transformation,[],[f25])).
% 3.02/0.99  
% 3.02/0.99  fof(f13,axiom,(
% 3.02/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/0.99  
% 3.02/0.99  fof(f33,plain,(
% 3.02/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.02/0.99    inference(ennf_transformation,[],[f13])).
% 3.02/0.99  
% 3.02/0.99  fof(f75,plain,(
% 3.02/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.02/0.99    inference(cnf_transformation,[],[f33])).
% 3.02/0.99  
% 3.02/0.99  fof(f94,plain,(
% 3.02/0.99    k1_xboole_0 = sK2 | k1_xboole_0 != sK3),
% 3.02/0.99    inference(cnf_transformation,[],[f55])).
% 3.02/0.99  
% 3.02/0.99  fof(f16,axiom,(
% 3.02/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/0.99  
% 3.02/0.99  fof(f38,plain,(
% 3.02/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.02/0.99    inference(ennf_transformation,[],[f16])).
% 3.02/0.99  
% 3.02/0.99  fof(f39,plain,(
% 3.02/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.02/0.99    inference(flattening,[],[f38])).
% 3.02/0.99  
% 3.02/0.99  fof(f53,plain,(
% 3.02/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.02/0.99    inference(nnf_transformation,[],[f39])).
% 3.02/0.99  
% 3.02/0.99  fof(f79,plain,(
% 3.02/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.02/0.99    inference(cnf_transformation,[],[f53])).
% 3.02/0.99  
% 3.02/0.99  fof(f103,plain,(
% 3.02/0.99    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.02/0.99    inference(equality_resolution,[],[f79])).
% 3.02/0.99  
% 3.02/0.99  fof(f12,axiom,(
% 3.02/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/0.99  
% 3.02/0.99  fof(f32,plain,(
% 3.02/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.02/0.99    inference(ennf_transformation,[],[f12])).
% 3.02/0.99  
% 3.02/0.99  fof(f74,plain,(
% 3.02/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.02/0.99    inference(cnf_transformation,[],[f32])).
% 3.02/0.99  
% 3.02/0.99  fof(f81,plain,(
% 3.02/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.02/0.99    inference(cnf_transformation,[],[f53])).
% 3.02/0.99  
% 3.02/0.99  fof(f102,plain,(
% 3.02/0.99    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.02/0.99    inference(equality_resolution,[],[f81])).
% 3.02/0.99  
% 3.02/0.99  fof(f14,axiom,(
% 3.02/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_tarski(k2_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))),
% 3.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/0.99  
% 3.02/0.99  fof(f34,plain,(
% 3.02/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 3.02/0.99    inference(ennf_transformation,[],[f14])).
% 3.02/0.99  
% 3.02/0.99  fof(f35,plain,(
% 3.02/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 3.02/0.99    inference(flattening,[],[f34])).
% 3.02/0.99  
% 3.02/0.99  fof(f76,plain,(
% 3.02/0.99    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) )),
% 3.02/0.99    inference(cnf_transformation,[],[f35])).
% 3.02/0.99  
% 3.02/0.99  fof(f6,axiom,(
% 3.02/0.99    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 3.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/0.99  
% 3.02/0.99  fof(f26,plain,(
% 3.02/0.99    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 3.02/0.99    inference(ennf_transformation,[],[f6])).
% 3.02/0.99  
% 3.02/0.99  fof(f67,plain,(
% 3.02/0.99    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 3.02/0.99    inference(cnf_transformation,[],[f26])).
% 3.02/0.99  
% 3.02/0.99  fof(f66,plain,(
% 3.02/0.99    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 3.02/0.99    inference(cnf_transformation,[],[f26])).
% 3.02/0.99  
% 3.02/0.99  fof(f98,plain,(
% 3.02/0.99    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 3.02/0.99    inference(equality_resolution,[],[f66])).
% 3.02/0.99  
% 3.02/0.99  cnf(c_8,plain,
% 3.02/0.99      ( r1_tarski(X0,X0) ),
% 3.02/0.99      inference(cnf_transformation,[],[f97]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1483,plain,
% 3.02/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_37,negated_conjecture,
% 3.02/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 3.02/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1466,plain,
% 3.02/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_29,plain,
% 3.02/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.02/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 3.02/0.99      | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
% 3.02/0.99      | ~ v1_funct_1(X0)
% 3.02/0.99      | k1_xboole_0 = X2 ),
% 3.02/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_39,negated_conjecture,
% 3.02/0.99      ( v1_funct_1(sK5) ),
% 3.02/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_559,plain,
% 3.02/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.02/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 3.02/0.99      | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
% 3.02/0.99      | sK5 != X0
% 3.02/0.99      | k1_xboole_0 = X2 ),
% 3.02/0.99      inference(resolution_lifted,[status(thm)],[c_29,c_39]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_560,plain,
% 3.02/0.99      ( ~ v1_funct_2(sK5,X0,X1)
% 3.02/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.02/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
% 3.02/0.99      | ~ r1_tarski(k2_relset_1(X0,X1,sK5),X2)
% 3.02/0.99      | k1_xboole_0 = X1 ),
% 3.02/0.99      inference(unflattening,[status(thm)],[c_559]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1460,plain,
% 3.02/0.99      ( k1_xboole_0 = X0
% 3.02/0.99      | v1_funct_2(sK5,X1,X0) != iProver_top
% 3.02/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
% 3.02/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.02/0.99      | r1_tarski(k2_relset_1(X1,X0,sK5),X2) != iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_560]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1878,plain,
% 3.02/0.99      ( sK3 = k1_xboole_0
% 3.02/0.99      | v1_funct_2(sK5,sK2,sK3) != iProver_top
% 3.02/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 3.02/0.99      | r1_tarski(k2_relset_1(sK2,sK3,sK5),X0) != iProver_top ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_1466,c_1460]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_38,negated_conjecture,
% 3.02/0.99      ( v1_funct_2(sK5,sK2,sK3) ),
% 3.02/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_41,plain,
% 3.02/0.99      ( v1_funct_2(sK5,sK2,sK3) = iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2199,plain,
% 3.02/0.99      ( sK3 = k1_xboole_0
% 3.02/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 3.02/0.99      | r1_tarski(k2_relset_1(sK2,sK3,sK5),X0) != iProver_top ),
% 3.02/0.99      inference(global_propositional_subsumption,
% 3.02/0.99                [status(thm)],
% 3.02/0.99                [c_1878,c_41]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2208,plain,
% 3.02/0.99      ( sK3 = k1_xboole_0
% 3.02/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relset_1(sK2,sK3,sK5)))) = iProver_top ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_1483,c_2199]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2268,plain,
% 3.02/0.99      ( k2_relset_1(sK2,sK3,sK5) = k1_xboole_0
% 3.02/0.99      | sK3 = k1_xboole_0
% 3.02/0.99      | v1_funct_2(sK5,sK2,k2_relset_1(sK2,sK3,sK5)) != iProver_top
% 3.02/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 3.02/0.99      | r1_tarski(k2_relset_1(sK2,k2_relset_1(sK2,sK3,sK5),sK5),X0) != iProver_top ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_2208,c_1460]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_31,plain,
% 3.02/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.02/0.99      | v1_funct_2(X0,X1,X3)
% 3.02/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/0.99      | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
% 3.02/0.99      | ~ v1_funct_1(X0)
% 3.02/0.99      | k1_xboole_0 = X2 ),
% 3.02/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_524,plain,
% 3.02/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.02/0.99      | v1_funct_2(X0,X1,X3)
% 3.02/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/0.99      | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
% 3.02/0.99      | sK5 != X0
% 3.02/0.99      | k1_xboole_0 = X2 ),
% 3.02/0.99      inference(resolution_lifted,[status(thm)],[c_31,c_39]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_525,plain,
% 3.02/0.99      ( ~ v1_funct_2(sK5,X0,X1)
% 3.02/0.99      | v1_funct_2(sK5,X0,X2)
% 3.02/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.02/0.99      | ~ r1_tarski(k2_relset_1(X0,X1,sK5),X2)
% 3.02/0.99      | k1_xboole_0 = X1 ),
% 3.02/0.99      inference(unflattening,[status(thm)],[c_524]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1462,plain,
% 3.02/0.99      ( k1_xboole_0 = X0
% 3.02/0.99      | v1_funct_2(sK5,X1,X0) != iProver_top
% 3.02/0.99      | v1_funct_2(sK5,X1,X2) = iProver_top
% 3.02/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
% 3.02/0.99      | r1_tarski(k2_relset_1(X1,X0,sK5),X2) != iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_525]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1841,plain,
% 3.02/0.99      ( sK3 = k1_xboole_0
% 3.02/0.99      | v1_funct_2(sK5,sK2,X0) = iProver_top
% 3.02/0.99      | v1_funct_2(sK5,sK2,sK3) != iProver_top
% 3.02/0.99      | r1_tarski(k2_relset_1(sK2,sK3,sK5),X0) != iProver_top ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_1466,c_1462]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2085,plain,
% 3.02/0.99      ( v1_funct_2(sK5,sK2,X0) = iProver_top
% 3.02/0.99      | sK3 = k1_xboole_0
% 3.02/0.99      | r1_tarski(k2_relset_1(sK2,sK3,sK5),X0) != iProver_top ),
% 3.02/0.99      inference(global_propositional_subsumption,
% 3.02/0.99                [status(thm)],
% 3.02/0.99                [c_1841,c_41]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2086,plain,
% 3.02/0.99      ( sK3 = k1_xboole_0
% 3.02/0.99      | v1_funct_2(sK5,sK2,X0) = iProver_top
% 3.02/0.99      | r1_tarski(k2_relset_1(sK2,sK3,sK5),X0) != iProver_top ),
% 3.02/0.99      inference(renaming,[status(thm)],[c_2085]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2094,plain,
% 3.02/0.99      ( sK3 = k1_xboole_0
% 3.02/0.99      | v1_funct_2(sK5,sK2,k2_relset_1(sK2,sK3,sK5)) = iProver_top ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_1483,c_2086]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2345,plain,
% 3.02/0.99      ( sK3 = k1_xboole_0
% 3.02/0.99      | k2_relset_1(sK2,sK3,sK5) = k1_xboole_0
% 3.02/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 3.02/0.99      | r1_tarski(k2_relset_1(sK2,k2_relset_1(sK2,sK3,sK5),sK5),X0) != iProver_top ),
% 3.02/0.99      inference(global_propositional_subsumption,
% 3.02/0.99                [status(thm)],
% 3.02/0.99                [c_2268,c_2094]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2346,plain,
% 3.02/0.99      ( k2_relset_1(sK2,sK3,sK5) = k1_xboole_0
% 3.02/0.99      | sK3 = k1_xboole_0
% 3.02/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 3.02/0.99      | r1_tarski(k2_relset_1(sK2,k2_relset_1(sK2,sK3,sK5),sK5),X0) != iProver_top ),
% 3.02/0.99      inference(renaming,[status(thm)],[c_2345]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2355,plain,
% 3.02/0.99      ( k2_relset_1(sK2,sK3,sK5) = k1_xboole_0
% 3.02/0.99      | sK3 = k1_xboole_0
% 3.02/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relset_1(sK2,k2_relset_1(sK2,sK3,sK5),sK5)))) = iProver_top ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_1483,c_2346]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_13,plain,
% 3.02/0.99      ( ~ v5_relat_1(X0,X1)
% 3.02/0.99      | r1_tarski(k2_relat_1(X0),X1)
% 3.02/0.99      | ~ v1_relat_1(X0) ),
% 3.02/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_16,plain,
% 3.02/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/0.99      | v5_relat_1(X0,X2) ),
% 3.02/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_443,plain,
% 3.02/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/0.99      | r1_tarski(k2_relat_1(X3),X4)
% 3.02/0.99      | ~ v1_relat_1(X3)
% 3.02/0.99      | X0 != X3
% 3.02/0.99      | X2 != X4 ),
% 3.02/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_16]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_444,plain,
% 3.02/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/0.99      | r1_tarski(k2_relat_1(X0),X2)
% 3.02/0.99      | ~ v1_relat_1(X0) ),
% 3.02/0.99      inference(unflattening,[status(thm)],[c_443]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_15,plain,
% 3.02/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/0.99      | v1_relat_1(X0) ),
% 3.02/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_448,plain,
% 3.02/0.99      ( r1_tarski(k2_relat_1(X0),X2)
% 3.02/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.02/0.99      inference(global_propositional_subsumption,
% 3.02/0.99                [status(thm)],
% 3.02/0.99                [c_444,c_15]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_449,plain,
% 3.02/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/0.99      | r1_tarski(k2_relat_1(X0),X2) ),
% 3.02/0.99      inference(renaming,[status(thm)],[c_448]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1463,plain,
% 3.02/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.02/0.99      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_449]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2482,plain,
% 3.02/0.99      ( k2_relset_1(sK2,sK3,sK5) = k1_xboole_0
% 3.02/0.99      | sK3 = k1_xboole_0
% 3.02/0.99      | r1_tarski(k2_relat_1(sK5),k2_relset_1(sK2,k2_relset_1(sK2,sK3,sK5),sK5)) = iProver_top ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_2355,c_1463]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_42,plain,
% 3.02/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_36,negated_conjecture,
% 3.02/0.99      ( r1_tarski(sK3,sK4) ),
% 3.02/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_43,plain,
% 3.02/0.99      ( r1_tarski(sK3,sK4) = iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_34,negated_conjecture,
% 3.02/0.99      ( ~ v1_funct_2(sK5,sK2,sK4)
% 3.02/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
% 3.02/0.99      | ~ v1_funct_1(sK5) ),
% 3.02/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_202,plain,
% 3.02/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
% 3.02/0.99      | ~ v1_funct_2(sK5,sK2,sK4) ),
% 3.02/0.99      inference(global_propositional_subsumption,
% 3.02/0.99                [status(thm)],
% 3.02/0.99                [c_34,c_39]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_203,negated_conjecture,
% 3.02/0.99      ( ~ v1_funct_2(sK5,sK2,sK4)
% 3.02/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) ),
% 3.02/0.99      inference(renaming,[status(thm)],[c_202]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_204,plain,
% 3.02/0.99      ( v1_funct_2(sK5,sK2,sK4) != iProver_top
% 3.02/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_203]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_21,plain,
% 3.02/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 3.02/0.99      | ~ r1_tarski(X1,X3)
% 3.02/0.99      | ~ r1_tarski(X2,X4) ),
% 3.02/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1810,plain,
% 3.02/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.02/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.02/0.99      | ~ r1_tarski(sK3,X1)
% 3.02/0.99      | ~ r1_tarski(sK2,X0) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_21]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1953,plain,
% 3.02/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,sK4)))
% 3.02/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.02/0.99      | ~ r1_tarski(sK3,sK4)
% 3.02/0.99      | ~ r1_tarski(sK2,X0) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_1810]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1998,plain,
% 3.02/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.02/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
% 3.02/0.99      | ~ r1_tarski(sK3,sK4)
% 3.02/0.99      | ~ r1_tarski(sK2,sK2) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_1953]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2000,plain,
% 3.02/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 3.02/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) = iProver_top
% 3.02/0.99      | r1_tarski(sK3,sK4) != iProver_top
% 3.02/0.99      | r1_tarski(sK2,sK2) != iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_1998]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1999,plain,
% 3.02/0.99      ( r1_tarski(sK2,sK2) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2002,plain,
% 3.02/0.99      ( r1_tarski(sK2,sK2) = iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_1999]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1467,plain,
% 3.02/0.99      ( r1_tarski(sK3,sK4) = iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1474,plain,
% 3.02/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.02/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) = iProver_top
% 3.02/0.99      | r1_tarski(X1,X3) != iProver_top
% 3.02/0.99      | r1_tarski(X2,X4) != iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_5066,plain,
% 3.02/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
% 3.02/0.99      | r1_tarski(sK3,X1) != iProver_top
% 3.02/0.99      | r1_tarski(sK2,X0) != iProver_top ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_1466,c_1474]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_5102,plain,
% 3.02/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
% 3.02/0.99      | r1_tarski(X2,X0) != iProver_top
% 3.02/0.99      | r1_tarski(X3,X1) != iProver_top
% 3.02/0.99      | r1_tarski(sK3,X3) != iProver_top
% 3.02/0.99      | r1_tarski(sK2,X2) != iProver_top ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_5066,c_1474]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_6301,plain,
% 3.02/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,sK4))) = iProver_top
% 3.02/0.99      | r1_tarski(X1,X0) != iProver_top
% 3.02/0.99      | r1_tarski(sK3,sK3) != iProver_top
% 3.02/0.99      | r1_tarski(sK2,X1) != iProver_top ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_1467,c_5102]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1946,plain,
% 3.02/0.99      ( r1_tarski(sK3,sK3) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1951,plain,
% 3.02/0.99      ( r1_tarski(sK3,sK3) = iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_1946]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_6346,plain,
% 3.02/0.99      ( r1_tarski(X1,X0) != iProver_top
% 3.02/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,sK4))) = iProver_top
% 3.02/0.99      | r1_tarski(sK2,X1) != iProver_top ),
% 3.02/0.99      inference(global_propositional_subsumption,
% 3.02/0.99                [status(thm)],
% 3.02/0.99                [c_6301,c_1951]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_6347,plain,
% 3.02/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,sK4))) = iProver_top
% 3.02/0.99      | r1_tarski(X1,X0) != iProver_top
% 3.02/0.99      | r1_tarski(sK2,X1) != iProver_top ),
% 3.02/0.99      inference(renaming,[status(thm)],[c_6346]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_6356,plain,
% 3.02/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) = iProver_top
% 3.02/0.99      | r1_tarski(sK2,sK3) != iProver_top ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_1467,c_6347]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_6522,plain,
% 3.02/0.99      ( r1_tarski(k2_relat_1(sK5),sK4) = iProver_top
% 3.02/0.99      | r1_tarski(sK2,sK3) != iProver_top ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_6356,c_1463]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1758,plain,
% 3.02/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.02/0.99      | r1_tarski(k2_relat_1(sK5),sK3) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_449]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1759,plain,
% 3.02/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 3.02/0.99      | r1_tarski(k2_relat_1(sK5),sK3) = iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_1758]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_9,plain,
% 3.02/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 3.02/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1779,plain,
% 3.02/0.99      ( ~ r1_tarski(X0,X1)
% 3.02/0.99      | ~ r1_tarski(k2_relat_1(X2),X0)
% 3.02/0.99      | r1_tarski(k2_relat_1(X2),X1) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1896,plain,
% 3.02/0.99      ( r1_tarski(k2_relat_1(sK5),X0)
% 3.02/0.99      | ~ r1_tarski(k2_relat_1(sK5),sK3)
% 3.02/0.99      | ~ r1_tarski(sK3,X0) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_1779]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2132,plain,
% 3.02/0.99      ( ~ r1_tarski(k2_relat_1(sK5),sK3)
% 3.02/0.99      | r1_tarski(k2_relat_1(sK5),sK4)
% 3.02/0.99      | ~ r1_tarski(sK3,sK4) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_1896]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2133,plain,
% 3.02/0.99      ( r1_tarski(k2_relat_1(sK5),sK3) != iProver_top
% 3.02/0.99      | r1_tarski(k2_relat_1(sK5),sK4) = iProver_top
% 3.02/0.99      | r1_tarski(sK3,sK4) != iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_2132]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_6606,plain,
% 3.02/0.99      ( r1_tarski(k2_relat_1(sK5),sK4) = iProver_top ),
% 3.02/0.99      inference(global_propositional_subsumption,
% 3.02/0.99                [status(thm)],
% 3.02/0.99                [c_6522,c_42,c_43,c_1759,c_2133]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_19,plain,
% 3.02/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.02/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1476,plain,
% 3.02/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.02/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3436,plain,
% 3.02/0.99      ( k2_relset_1(sK2,sK3,sK5) = k2_relat_1(sK5) ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_1466,c_1476]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3719,plain,
% 3.02/0.99      ( sK3 = k1_xboole_0
% 3.02/0.99      | v1_funct_2(sK5,sK2,X0) = iProver_top
% 3.02/0.99      | r1_tarski(k2_relat_1(sK5),X0) != iProver_top ),
% 3.02/0.99      inference(demodulation,[status(thm)],[c_3436,c_2086]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_6615,plain,
% 3.02/0.99      ( sK3 = k1_xboole_0 | v1_funct_2(sK5,sK2,sK4) = iProver_top ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_6606,c_3719]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_7015,plain,
% 3.02/0.99      ( sK3 = k1_xboole_0 ),
% 3.02/0.99      inference(global_propositional_subsumption,
% 3.02/0.99                [status(thm)],
% 3.02/0.99                [c_2482,c_42,c_43,c_204,c_2000,c_2002,c_6615]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_7032,plain,
% 3.02/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
% 3.02/0.99      inference(demodulation,[status(thm)],[c_7015,c_1466]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_35,negated_conjecture,
% 3.02/0.99      ( k1_xboole_0 != sK3 | k1_xboole_0 = sK2 ),
% 3.02/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_7035,plain,
% 3.02/0.99      ( sK2 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.02/0.99      inference(demodulation,[status(thm)],[c_7015,c_35]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_7036,plain,
% 3.02/0.99      ( sK2 = k1_xboole_0 ),
% 3.02/0.99      inference(equality_resolution_simp,[status(thm)],[c_7035]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_7044,plain,
% 3.02/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.02/0.99      inference(light_normalisation,[status(thm)],[c_7032,c_7036]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_26,plain,
% 3.02/0.99      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 3.02/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.02/0.99      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 3.02/0.99      inference(cnf_transformation,[],[f103]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1469,plain,
% 3.02/0.99      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
% 3.02/0.99      | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
% 3.02/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_8165,plain,
% 3.02/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_xboole_0
% 3.02/0.99      | v1_funct_2(sK5,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_7044,c_1469]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_18,plain,
% 3.02/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.02/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1477,plain,
% 3.02/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.02/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3484,plain,
% 3.02/0.99      ( k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5) ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_1466,c_1477]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_7029,plain,
% 3.02/0.99      ( k1_relset_1(sK2,k1_xboole_0,sK5) = k1_relat_1(sK5) ),
% 3.02/0.99      inference(demodulation,[status(thm)],[c_7015,c_3484]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_7052,plain,
% 3.02/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_relat_1(sK5) ),
% 3.02/0.99      inference(light_normalisation,[status(thm)],[c_7029,c_7036]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_8183,plain,
% 3.02/0.99      ( k1_relat_1(sK5) = k1_xboole_0
% 3.02/0.99      | v1_funct_2(sK5,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.02/0.99      inference(demodulation,[status(thm)],[c_8165,c_7052]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_5107,plain,
% 3.02/0.99      ( k1_relset_1(X0,X1,sK5) = k1_relat_1(sK5)
% 3.02/0.99      | r1_tarski(sK3,X1) != iProver_top
% 3.02/0.99      | r1_tarski(sK2,X0) != iProver_top ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_5066,c_1477]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_5377,plain,
% 3.02/0.99      ( k1_relset_1(X0,sK4,sK5) = k1_relat_1(sK5)
% 3.02/0.99      | r1_tarski(sK2,X0) != iProver_top ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_1467,c_5107]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_5395,plain,
% 3.02/0.99      ( k1_relset_1(sK2,sK4,sK5) = k1_relat_1(sK5) ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_1483,c_5377]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_7149,plain,
% 3.02/0.99      ( k1_relset_1(k1_xboole_0,sK4,sK5) = k1_relat_1(sK5) ),
% 3.02/0.99      inference(demodulation,[status(thm)],[c_7036,c_5395]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_24,plain,
% 3.02/0.99      ( v1_funct_2(X0,k1_xboole_0,X1)
% 3.02/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.02/0.99      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 3.02/0.99      inference(cnf_transformation,[],[f102]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1471,plain,
% 3.02/0.99      ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
% 3.02/0.99      | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
% 3.02/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_7846,plain,
% 3.02/0.99      ( k1_relat_1(sK5) != k1_xboole_0
% 3.02/0.99      | v1_funct_2(sK5,k1_xboole_0,sK4) = iProver_top
% 3.02/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4))) != iProver_top ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_7149,c_1471]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3718,plain,
% 3.02/0.99      ( sK3 = k1_xboole_0
% 3.02/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 3.02/0.99      | r1_tarski(k2_relat_1(sK5),X0) != iProver_top ),
% 3.02/0.99      inference(demodulation,[status(thm)],[c_3436,c_2199]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_20,plain,
% 3.02/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 3.02/0.99      | ~ r1_tarski(k2_relat_1(X0),X3) ),
% 3.02/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2541,plain,
% 3.02/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.02/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
% 3.02/0.99      | ~ r1_tarski(k2_relat_1(sK5),X2) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_20]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3940,plain,
% 3.02/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
% 3.02/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
% 3.02/0.99      | ~ r1_tarski(k2_relat_1(sK5),X0) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_2541]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3941,plain,
% 3.02/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 3.02/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top
% 3.02/0.99      | r1_tarski(k2_relat_1(sK5),X0) != iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_3940]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4796,plain,
% 3.02/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 3.02/0.99      | r1_tarski(k2_relat_1(sK5),X0) != iProver_top ),
% 3.02/0.99      inference(global_propositional_subsumption,
% 3.02/0.99                [status(thm)],
% 3.02/0.99                [c_3718,c_42,c_43,c_2000,c_2002,c_3941]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1464,plain,
% 3.02/0.99      ( v1_funct_2(sK5,sK2,sK4) != iProver_top
% 3.02/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_203]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4806,plain,
% 3.02/0.99      ( v1_funct_2(sK5,sK2,sK4) != iProver_top
% 3.02/0.99      | r1_tarski(k2_relat_1(sK5),sK4) != iProver_top ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_4796,c_1464]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4863,plain,
% 3.02/0.99      ( v1_funct_2(sK5,sK2,sK4) != iProver_top ),
% 3.02/0.99      inference(global_propositional_subsumption,
% 3.02/0.99                [status(thm)],
% 3.02/0.99                [c_4806,c_42,c_43,c_204,c_2000,c_2002]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_7151,plain,
% 3.02/0.99      ( v1_funct_2(sK5,k1_xboole_0,sK4) != iProver_top ),
% 3.02/0.99      inference(demodulation,[status(thm)],[c_7036,c_4863]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_892,plain,
% 3.02/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.02/0.99      theory(equality) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2004,plain,
% 3.02/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(sK2,X2) | X2 != X1 | sK2 != X0 ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_892]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2908,plain,
% 3.02/0.99      ( ~ r1_tarski(sK2,X0) | r1_tarski(sK2,X1) | X1 != X0 | sK2 != sK2 ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_2004]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_5856,plain,
% 3.02/0.99      ( r1_tarski(sK2,X0)
% 3.02/0.99      | ~ r1_tarski(sK2,sK2)
% 3.02/0.99      | X0 != sK2
% 3.02/0.99      | sK2 != sK2 ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_2908]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_5857,plain,
% 3.02/0.99      ( X0 != sK2
% 3.02/0.99      | sK2 != sK2
% 3.02/0.99      | r1_tarski(sK2,X0) = iProver_top
% 3.02/0.99      | r1_tarski(sK2,sK2) != iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_5856]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_5859,plain,
% 3.02/0.99      ( sK2 != sK2
% 3.02/0.99      | k1_xboole_0 != sK2
% 3.02/0.99      | r1_tarski(sK2,sK2) != iProver_top
% 3.02/0.99      | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_5857]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3873,plain,
% 3.02/0.99      ( r1_tarski(sK4,sK4) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3878,plain,
% 3.02/0.99      ( r1_tarski(sK4,sK4) = iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_3873]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2387,plain,
% 3.02/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.02/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
% 3.02/0.99      | ~ r1_tarski(sK4,X1)
% 3.02/0.99      | ~ r1_tarski(sK2,X0) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_21]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3872,plain,
% 3.02/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,sK4)))
% 3.02/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
% 3.02/0.99      | ~ r1_tarski(sK4,sK4)
% 3.02/0.99      | ~ r1_tarski(sK2,X0) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_2387]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3874,plain,
% 3.02/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,sK4))) = iProver_top
% 3.02/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top
% 3.02/0.99      | r1_tarski(sK4,sK4) != iProver_top
% 3.02/0.99      | r1_tarski(sK2,X0) != iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_3872]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3876,plain,
% 3.02/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top
% 3.02/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4))) = iProver_top
% 3.02/0.99      | r1_tarski(sK4,sK4) != iProver_top
% 3.02/0.99      | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_3874]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_887,plain,( X0 = X0 ),theory(equality) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2909,plain,
% 3.02/0.99      ( sK2 = sK2 ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_887]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_898,plain,
% 3.02/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.02/0.99      | v1_funct_2(X3,X4,X5)
% 3.02/0.99      | X3 != X0
% 3.02/0.99      | X4 != X1
% 3.02/0.99      | X5 != X2 ),
% 3.02/0.99      theory(equality) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1825,plain,
% 3.02/0.99      ( v1_funct_2(X0,X1,X2)
% 3.02/0.99      | ~ v1_funct_2(sK5,sK2,sK3)
% 3.02/0.99      | X2 != sK3
% 3.02/0.99      | X1 != sK2
% 3.02/0.99      | X0 != sK5 ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_898]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2374,plain,
% 3.02/0.99      ( ~ v1_funct_2(sK5,sK2,sK3)
% 3.02/0.99      | v1_funct_2(sK5,k1_xboole_0,X0)
% 3.02/0.99      | X0 != sK3
% 3.02/0.99      | sK5 != sK5
% 3.02/0.99      | k1_xboole_0 != sK2 ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_1825]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2375,plain,
% 3.02/0.99      ( X0 != sK3
% 3.02/0.99      | sK5 != sK5
% 3.02/0.99      | k1_xboole_0 != sK2
% 3.02/0.99      | v1_funct_2(sK5,sK2,sK3) != iProver_top
% 3.02/0.99      | v1_funct_2(sK5,k1_xboole_0,X0) = iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_2374]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2377,plain,
% 3.02/0.99      ( sK5 != sK5
% 3.02/0.99      | k1_xboole_0 != sK3
% 3.02/0.99      | k1_xboole_0 != sK2
% 3.02/0.99      | v1_funct_2(sK5,sK2,sK3) != iProver_top
% 3.02/0.99      | v1_funct_2(sK5,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_2375]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1937,plain,
% 3.02/0.99      ( sK5 = sK5 ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_887]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_888,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1771,plain,
% 3.02/0.99      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_888]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1772,plain,
% 3.02/0.99      ( sK3 != k1_xboole_0
% 3.02/0.99      | k1_xboole_0 = sK3
% 3.02/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_1771]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_10,plain,
% 3.02/0.99      ( ~ r1_xboole_0(X0,X0) | k1_xboole_0 = X0 ),
% 3.02/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_95,plain,
% 3.02/0.99      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 3.02/0.99      | k1_xboole_0 = k1_xboole_0 ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_11,plain,
% 3.02/0.99      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 3.02/0.99      inference(cnf_transformation,[],[f98]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(contradiction,plain,
% 3.02/0.99      ( $false ),
% 3.02/0.99      inference(minisat,
% 3.02/0.99                [status(thm)],
% 3.02/0.99                [c_8183,c_7846,c_7151,c_6615,c_5859,c_3878,c_3876,c_2909,
% 3.02/0.99                 c_2377,c_2002,c_2000,c_1937,c_1772,c_204,c_95,c_11,c_35,
% 3.02/0.99                 c_43,c_42,c_41]) ).
% 3.02/0.99  
% 3.02/0.99  
% 3.02/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.02/0.99  
% 3.02/0.99  ------                               Statistics
% 3.02/0.99  
% 3.02/0.99  ------ General
% 3.02/0.99  
% 3.02/0.99  abstr_ref_over_cycles:                  0
% 3.02/0.99  abstr_ref_under_cycles:                 0
% 3.02/0.99  gc_basic_clause_elim:                   0
% 3.02/0.99  forced_gc_time:                         0
% 3.02/0.99  parsing_time:                           0.009
% 3.02/0.99  unif_index_cands_time:                  0.
% 3.02/0.99  unif_index_add_time:                    0.
% 3.02/0.99  orderings_time:                         0.
% 3.02/0.99  out_proof_time:                         0.013
% 3.02/0.99  total_time:                             0.23
% 3.02/0.99  num_of_symbols:                         53
% 3.02/0.99  num_of_terms:                           4544
% 3.02/0.99  
% 3.02/0.99  ------ Preprocessing
% 3.02/0.99  
% 3.02/0.99  num_of_splits:                          0
% 3.02/0.99  num_of_split_atoms:                     0
% 3.02/0.99  num_of_reused_defs:                     0
% 3.02/0.99  num_eq_ax_congr_red:                    31
% 3.02/0.99  num_of_sem_filtered_clauses:            1
% 3.02/0.99  num_of_subtypes:                        0
% 3.02/0.99  monotx_restored_types:                  0
% 3.02/0.99  sat_num_of_epr_types:                   0
% 3.02/0.99  sat_num_of_non_cyclic_types:            0
% 3.02/0.99  sat_guarded_non_collapsed_types:        0
% 3.02/0.99  num_pure_diseq_elim:                    0
% 3.02/0.99  simp_replaced_by:                       0
% 3.02/0.99  res_preprocessed:                       161
% 3.02/0.99  prep_upred:                             0
% 3.02/0.99  prep_unflattend:                        20
% 3.02/0.99  smt_new_axioms:                         0
% 3.02/0.99  pred_elim_cands:                        6
% 3.02/0.99  pred_elim:                              3
% 3.02/0.99  pred_elim_cl:                           4
% 3.02/0.99  pred_elim_cycles:                       7
% 3.02/0.99  merged_defs:                            0
% 3.02/0.99  merged_defs_ncl:                        0
% 3.02/0.99  bin_hyper_res:                          0
% 3.02/0.99  prep_cycles:                            4
% 3.02/0.99  pred_elim_time:                         0.005
% 3.02/0.99  splitting_time:                         0.
% 3.02/0.99  sem_filter_time:                        0.
% 3.02/0.99  monotx_time:                            0.001
% 3.02/0.99  subtype_inf_time:                       0.
% 3.02/0.99  
% 3.02/0.99  ------ Problem properties
% 3.02/0.99  
% 3.02/0.99  clauses:                                33
% 3.02/0.99  conjectures:                            5
% 3.02/0.99  epr:                                    11
% 3.02/0.99  horn:                                   24
% 3.02/0.99  ground:                                 6
% 3.02/0.99  unary:                                  5
% 3.02/0.99  binary:                                 12
% 3.02/0.99  lits:                                   87
% 3.02/0.99  lits_eq:                                18
% 3.02/0.99  fd_pure:                                0
% 3.02/0.99  fd_pseudo:                              0
% 3.02/0.99  fd_cond:                                7
% 3.02/0.99  fd_pseudo_cond:                         1
% 3.02/0.99  ac_symbols:                             0
% 3.02/0.99  
% 3.02/0.99  ------ Propositional Solver
% 3.02/0.99  
% 3.02/0.99  prop_solver_calls:                      29
% 3.02/0.99  prop_fast_solver_calls:                 1243
% 3.02/0.99  smt_solver_calls:                       0
% 3.02/0.99  smt_fast_solver_calls:                  0
% 3.02/0.99  prop_num_of_clauses:                    2753
% 3.02/0.99  prop_preprocess_simplified:             8357
% 3.02/0.99  prop_fo_subsumed:                       26
% 3.02/0.99  prop_solver_time:                       0.
% 3.02/0.99  smt_solver_time:                        0.
% 3.02/0.99  smt_fast_solver_time:                   0.
% 3.02/0.99  prop_fast_solver_time:                  0.
% 3.02/0.99  prop_unsat_core_time:                   0.
% 3.02/0.99  
% 3.02/0.99  ------ QBF
% 3.02/0.99  
% 3.02/0.99  qbf_q_res:                              0
% 3.02/0.99  qbf_num_tautologies:                    0
% 3.02/0.99  qbf_prep_cycles:                        0
% 3.02/0.99  
% 3.02/0.99  ------ BMC1
% 3.02/0.99  
% 3.02/0.99  bmc1_current_bound:                     -1
% 3.02/0.99  bmc1_last_solved_bound:                 -1
% 3.02/0.99  bmc1_unsat_core_size:                   -1
% 3.02/0.99  bmc1_unsat_core_parents_size:           -1
% 3.02/0.99  bmc1_merge_next_fun:                    0
% 3.02/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.02/0.99  
% 3.02/0.99  ------ Instantiation
% 3.02/0.99  
% 3.02/0.99  inst_num_of_clauses:                    816
% 3.02/0.99  inst_num_in_passive:                    391
% 3.02/0.99  inst_num_in_active:                     360
% 3.02/0.99  inst_num_in_unprocessed:                65
% 3.02/0.99  inst_num_of_loops:                      500
% 3.02/0.99  inst_num_of_learning_restarts:          0
% 3.02/0.99  inst_num_moves_active_passive:          137
% 3.02/0.99  inst_lit_activity:                      0
% 3.02/0.99  inst_lit_activity_moves:                0
% 3.02/0.99  inst_num_tautologies:                   0
% 3.02/0.99  inst_num_prop_implied:                  0
% 3.02/0.99  inst_num_existing_simplified:           0
% 3.02/0.99  inst_num_eq_res_simplified:             0
% 3.02/0.99  inst_num_child_elim:                    0
% 3.02/0.99  inst_num_of_dismatching_blockings:      204
% 3.02/0.99  inst_num_of_non_proper_insts:           806
% 3.02/0.99  inst_num_of_duplicates:                 0
% 3.02/0.99  inst_inst_num_from_inst_to_res:         0
% 3.02/0.99  inst_dismatching_checking_time:         0.
% 3.02/0.99  
% 3.02/0.99  ------ Resolution
% 3.02/0.99  
% 3.02/0.99  res_num_of_clauses:                     0
% 3.02/0.99  res_num_in_passive:                     0
% 3.02/0.99  res_num_in_active:                      0
% 3.02/0.99  res_num_of_loops:                       165
% 3.02/0.99  res_forward_subset_subsumed:            80
% 3.02/0.99  res_backward_subset_subsumed:           0
% 3.02/0.99  res_forward_subsumed:                   0
% 3.02/0.99  res_backward_subsumed:                  0
% 3.02/0.99  res_forward_subsumption_resolution:     0
% 3.02/0.99  res_backward_subsumption_resolution:    0
% 3.02/0.99  res_clause_to_clause_subsumption:       501
% 3.02/0.99  res_orphan_elimination:                 0
% 3.02/0.99  res_tautology_del:                      110
% 3.02/0.99  res_num_eq_res_simplified:              0
% 3.02/0.99  res_num_sel_changes:                    0
% 3.02/0.99  res_moves_from_active_to_pass:          0
% 3.02/0.99  
% 3.02/0.99  ------ Superposition
% 3.02/0.99  
% 3.02/0.99  sup_time_total:                         0.
% 3.02/0.99  sup_time_generating:                    0.
% 3.02/0.99  sup_time_sim_full:                      0.
% 3.02/0.99  sup_time_sim_immed:                     0.
% 3.02/0.99  
% 3.02/0.99  sup_num_of_clauses:                     135
% 3.02/0.99  sup_num_in_active:                      52
% 3.02/0.99  sup_num_in_passive:                     83
% 3.02/0.99  sup_num_of_loops:                       98
% 3.02/0.99  sup_fw_superposition:                   72
% 3.02/0.99  sup_bw_superposition:                   88
% 3.02/0.99  sup_immediate_simplified:               38
% 3.02/0.99  sup_given_eliminated:                   0
% 3.02/0.99  comparisons_done:                       0
% 3.02/0.99  comparisons_avoided:                    3
% 3.02/0.99  
% 3.02/0.99  ------ Simplifications
% 3.02/0.99  
% 3.02/0.99  
% 3.02/0.99  sim_fw_subset_subsumed:                 10
% 3.02/0.99  sim_bw_subset_subsumed:                 7
% 3.02/0.99  sim_fw_subsumed:                        8
% 3.02/0.99  sim_bw_subsumed:                        1
% 3.02/0.99  sim_fw_subsumption_res:                 0
% 3.02/0.99  sim_bw_subsumption_res:                 0
% 3.02/0.99  sim_tautology_del:                      3
% 3.02/0.99  sim_eq_tautology_del:                   8
% 3.02/0.99  sim_eq_res_simp:                        1
% 3.02/0.99  sim_fw_demodulated:                     2
% 3.02/0.99  sim_bw_demodulated:                     48
% 3.02/0.99  sim_light_normalised:                   18
% 3.02/0.99  sim_joinable_taut:                      0
% 3.02/0.99  sim_joinable_simp:                      0
% 3.02/0.99  sim_ac_normalised:                      0
% 3.02/0.99  sim_smt_subsumption:                    0
% 3.02/0.99  
%------------------------------------------------------------------------------
