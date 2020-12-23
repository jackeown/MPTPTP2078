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
% DateTime   : Thu Dec  3 12:00:35 EST 2020

% Result     : Theorem 7.71s
% Output     : CNFRefutation 7.71s
% Verified   : 
% Statistics : Number of formulae       :  303 (5055 expanded)
%              Number of clauses        :  211 (2109 expanded)
%              Number of leaves         :   25 ( 870 expanded)
%              Depth                    :   38
%              Number of atoms          :  869 (19470 expanded)
%              Number of equality atoms :  538 (7687 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
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
    inference(nnf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f90,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f20,conjecture,(
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

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
         => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_2(X3,X0,X2)
              & v1_funct_1(X3) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f38,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f39,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f38])).

fof(f49,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
          | ~ v1_funct_2(X3,X0,X2)
          | ~ v1_funct_1(X3) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(k2_relset_1(X0,X1,X3),X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
        | ~ v1_funct_2(sK4,sK1,sK3)
        | ~ v1_funct_1(sK4) )
      & ( k1_xboole_0 = sK1
        | k1_xboole_0 != sK2 )
      & r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK4,sK1,sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
      | ~ v1_funct_2(sK4,sK1,sK3)
      | ~ v1_funct_1(sK4) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 != sK2 )
    & r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f39,f49])).

fof(f85,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f50])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f86,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f18,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
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
    inference(nnf_transformation,[],[f6])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f13,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f5,axiom,(
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
    inference(nnf_transformation,[],[f5])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f44])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f91,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f59])).

fof(f70,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f54,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f92,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f58])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

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

fof(f36,plain,(
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

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

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
    inference(nnf_transformation,[],[f37])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f95,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f81])).

fof(f84,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f87,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f50])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f88,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(sK4,sK1,sK3)
    | ~ v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f50])).

fof(f83,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f50])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f96,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f80])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f93,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f82])).

fof(f94,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f93])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f69,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f40])).

fof(f51,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f24])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f68,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1422,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1410,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1414,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3776,plain,
    ( k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1410,c_1414])).

cnf(c_34,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1411,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_3941,plain,
    ( r1_tarski(k2_relat_1(sK4),sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3776,c_1411])).

cnf(c_24,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1413,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1415,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4123,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | r1_tarski(k2_relat_1(X2),X1) != iProver_top
    | r1_tarski(k1_relat_1(X2),X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1413,c_1415])).

cnf(c_35231,plain,
    ( k1_relset_1(X0,sK3,sK4) = k1_relat_1(sK4)
    | r1_tarski(k1_relat_1(sK4),X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3941,c_4123])).

cnf(c_15,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1419,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_25,plain,
    ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1412,plain,
    ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1420,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2832,plain,
    ( r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1412,c_1420])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_9,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_264,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_265,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_264])).

cnf(c_328,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_12,c_265])).

cnf(c_1409,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_328])).

cnf(c_6895,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X0)) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2832,c_1409])).

cnf(c_17992,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1419,c_6895])).

cnf(c_21,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_14,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_490,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_21,c_14])).

cnf(c_1407,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_490])).

cnf(c_1799,plain,
    ( r1_tarski(k1_relat_1(sK4),sK1) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1410,c_1407])).

cnf(c_19,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_6,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_3523,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1413,c_1420])).

cnf(c_10898,plain,
    ( r1_tarski(X0,k1_xboole_0) = iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_3523])).

cnf(c_1801,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_1407])).

cnf(c_3521,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_1413])).

cnf(c_4804,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1422,c_3521])).

cnf(c_11145,plain,
    ( r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | r1_tarski(X0,k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10898,c_1801,c_4804])).

cnf(c_11146,plain,
    ( r1_tarski(X0,k1_xboole_0) = iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_11145])).

cnf(c_11150,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | r1_tarski(k6_relat_1(X0),k1_xboole_0) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_19,c_11146])).

cnf(c_20,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1421,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4679,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1421,c_1801])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1423,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_15277,plain,
    ( k1_relat_1(X0) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4679,c_1423])).

cnf(c_7,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2948,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1421,c_1407])).

cnf(c_8476,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_2948])).

cnf(c_8492,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_relat_1(X0)) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8476,c_1409])).

cnf(c_87,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_89,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_87])).

cnf(c_8,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_106,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_107,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_114,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_116,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_114])).

cnf(c_1594,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_328])).

cnf(c_1595,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1594])).

cnf(c_1597,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1595])).

cnf(c_875,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1842,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k2_zfmisc_1(X3,X4))
    | X2 != X0
    | k2_zfmisc_1(X3,X4) != X1 ),
    inference(instantiation,[status(thm)],[c_875])).

cnf(c_1843,plain,
    ( X0 != X1
    | k2_zfmisc_1(X2,X3) != X4
    | r1_tarski(X1,X4) != iProver_top
    | r1_tarski(X0,k2_zfmisc_1(X2,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1842])).

cnf(c_1845,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1843])).

cnf(c_20138,plain,
    ( v1_relat_1(k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8492,c_89,c_106,c_107,c_116,c_1597,c_1845])).

cnf(c_20139,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_relat_1(X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_20138])).

cnf(c_20152,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top
    | v1_relat_1(k1_relat_1(k6_relat_1(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_11150,c_20139])).

cnf(c_20155,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_20152,c_20])).

cnf(c_22203,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_15277,c_17992,c_20155])).

cnf(c_22204,plain,
    ( k1_relat_1(X0) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_22203])).

cnf(c_22219,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(k6_relat_1(X0),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_20,c_22204])).

cnf(c_22223,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k6_relat_1(X1),k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_22219,c_20])).

cnf(c_22344,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,k1_xboole_0) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11150,c_22223])).

cnf(c_24490,plain,
    ( k1_relat_1(sK4) = sK1
    | r1_tarski(sK1,k1_xboole_0) != iProver_top
    | v1_relat_1(k6_relat_1(sK1)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1799,c_22344])).

cnf(c_1485,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK1,k1_xboole_0)
    | sK1 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_875])).

cnf(c_1486,plain,
    ( sK1 != X0
    | k1_xboole_0 != X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(sK1,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1485])).

cnf(c_1488,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK1,k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1486])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_36,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_540,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK2 != k1_xboole_0
    | sK1 != X1
    | sK4 != X0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_36])).

cnf(c_541,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | sK2 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_540])).

cnf(c_1405,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK4
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_541])).

cnf(c_1425,plain,
    ( sK2 != k1_xboole_0
    | sK1 = k1_xboole_0
    | sK4 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1405,c_6])).

cnf(c_33,negated_conjecture,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_874,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1462,plain,
    ( sK1 != X0
    | sK1 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_874])).

cnf(c_1517,plain,
    ( sK1 != sK1
    | sK1 = k1_xboole_0
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_1462])).

cnf(c_873,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1584,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_873])).

cnf(c_1704,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_874])).

cnf(c_1705,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1704])).

cnf(c_2056,plain,
    ( sK2 != k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1425,c_33,c_106,c_107,c_1517,c_1584,c_1705])).

cnf(c_2833,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1410,c_1420])).

cnf(c_2937,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2833,c_1409])).

cnf(c_3205,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1419,c_2937])).

cnf(c_31,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_602,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK2 != X2
    | sK1 != X1
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_36])).

cnf(c_603,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_602])).

cnf(c_605,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_603,c_35])).

cnf(c_4125,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1410,c_1415])).

cnf(c_4324,plain,
    ( k1_relat_1(sK4) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_605,c_4125])).

cnf(c_24756,plain,
    ( v1_relat_1(k6_relat_1(sK1)) != iProver_top
    | k1_relat_1(sK4) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_24490,c_106,c_107,c_116,c_1488,c_2056,c_3205,c_4324])).

cnf(c_24757,plain,
    ( k1_relat_1(sK4) = sK1
    | v1_relat_1(k6_relat_1(sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_24756])).

cnf(c_24760,plain,
    ( k1_relat_1(sK4) = sK1 ),
    inference(superposition,[status(thm)],[c_17992,c_24757])).

cnf(c_35236,plain,
    ( k1_relset_1(X0,sK3,sK4) = sK1
    | r1_tarski(sK1,X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_35231,c_24760])).

cnf(c_36666,plain,
    ( r1_tarski(sK1,X0) != iProver_top
    | k1_relset_1(X0,sK3,sK4) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_35236,c_3205])).

cnf(c_36667,plain,
    ( k1_relset_1(X0,sK3,sK4) = sK1
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_36666])).

cnf(c_36672,plain,
    ( k1_relset_1(sK1,sK3,sK4) = sK1 ),
    inference(superposition,[status(thm)],[c_1422,c_36667])).

cnf(c_29,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_32,negated_conjecture,
    ( ~ v1_funct_2(sK4,sK1,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_193,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(sK4,sK1,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_32,c_37])).

cnf(c_194,negated_conjecture,
    ( ~ v1_funct_2(sK4,sK1,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(renaming,[status(thm)],[c_193])).

cnf(c_589,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | k1_relset_1(X1,X2,X0) != X1
    | sK3 != X2
    | sK1 != X1
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_194])).

cnf(c_590,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | k1_relset_1(sK1,sK3,sK4) != sK1
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_589])).

cnf(c_1402,plain,
    ( k1_relset_1(sK1,sK3,sK4) != sK1
    | k1_xboole_0 = sK3
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_590])).

cnf(c_36864,plain,
    ( sK3 = k1_xboole_0
    | sK1 != sK1
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_36672,c_1402])).

cnf(c_36866,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_36864])).

cnf(c_1468,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ r1_tarski(k2_relat_1(sK4),sK3)
    | ~ r1_tarski(k1_relat_1(sK4),sK1)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_1800,plain,
    ( r1_tarski(k1_relat_1(sK4),sK1)
    | ~ v1_relat_1(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1799])).

cnf(c_1709,plain,
    ( sK3 != X0
    | sK3 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_874])).

cnf(c_1964,plain,
    ( sK3 != sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_1709])).

cnf(c_2700,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_873])).

cnf(c_3206,plain,
    ( v1_relat_1(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3205])).

cnf(c_3944,plain,
    ( r1_tarski(k2_relat_1(sK4),sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3941])).

cnf(c_36868,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_36866,c_590,c_1468,c_1800,c_1964,c_2700,c_3206,c_3944,c_36672])).

cnf(c_28,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_560,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | sK3 != X1
    | sK1 != k1_xboole_0
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_194])).

cnf(c_561,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)))
    | k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_560])).

cnf(c_1404,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_561])).

cnf(c_1426,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1404,c_7])).

cnf(c_36901,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_36868,c_1426])).

cnf(c_36904,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_36901,c_6])).

cnf(c_103,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_105,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_103])).

cnf(c_26,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_517,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | sK3 != k1_xboole_0
    | sK1 != X0
    | sK4 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_194])).

cnf(c_518,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | sK3 != k1_xboole_0
    | sK4 != k1_xboole_0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_517])).

cnf(c_1406,plain,
    ( sK3 != k1_xboole_0
    | sK4 != k1_xboole_0
    | k1_xboole_0 = sK1
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_518])).

cnf(c_1427,plain,
    ( sK3 != k1_xboole_0
    | sK1 = k1_xboole_0
    | sK4 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1406,c_6])).

cnf(c_1469,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) = iProver_top
    | r1_tarski(k2_relat_1(sK4),sK3) != iProver_top
    | r1_tarski(k1_relat_1(sK4),sK1) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1468])).

cnf(c_1587,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_873])).

cnf(c_1529,plain,
    ( X0 != X1
    | sK4 != X1
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_874])).

cnf(c_1653,plain,
    ( X0 != sK4
    | sK4 = X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1529])).

cnf(c_1654,plain,
    ( sK4 != sK4
    | sK4 = k1_xboole_0
    | k1_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_1653])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2593,plain,
    ( ~ v1_relat_1(sK4)
    | k2_relat_1(sK4) != k1_xboole_0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2602,plain,
    ( k2_relat_1(sK4) != k1_xboole_0
    | k1_xboole_0 = sK4
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2593])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_327,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(bin_hyper_res,[status(thm)],[c_11,c_265])).

cnf(c_454,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X1)
    | X0 != X2
    | sK0(X2) != X3
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_327])).

cnf(c_455,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X1)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_454])).

cnf(c_4,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_5,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_439,plain,
    ( ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_5])).

cnf(c_440,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_439])).

cnf(c_473,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,k1_xboole_0)
    | X2 != X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_455,c_440])).

cnf(c_474,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_473])).

cnf(c_1408,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_474])).

cnf(c_2307,plain,
    ( k2_relset_1(sK1,sK2,sK4) = k1_xboole_0
    | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1411,c_1408])).

cnf(c_3940,plain,
    ( k2_relat_1(sK4) = k1_xboole_0
    | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3776,c_2307])).

cnf(c_3943,plain,
    ( ~ r1_tarski(sK3,k1_xboole_0)
    | k2_relat_1(sK4) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3940])).

cnf(c_1956,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK3,k1_xboole_0)
    | sK3 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_875])).

cnf(c_2729,plain,
    ( ~ r1_tarski(sK3,X0)
    | r1_tarski(sK3,k1_xboole_0)
    | sK3 != sK3
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1956])).

cnf(c_4771,plain,
    ( ~ r1_tarski(sK3,sK3)
    | r1_tarski(sK3,k1_xboole_0)
    | sK3 != sK3
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_2729])).

cnf(c_4805,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(sK4),k1_xboole_0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1799,c_3521])).

cnf(c_4936,plain,
    ( r1_tarski(k2_relat_1(sK4),k1_xboole_0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4805,c_3205])).

cnf(c_4937,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(sK4),k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4936])).

cnf(c_6983,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(sK4),X2)
    | X2 != X1
    | k2_relat_1(sK4) != X0 ),
    inference(instantiation,[status(thm)],[c_875])).

cnf(c_6984,plain,
    ( X0 != X1
    | k2_relat_1(sK4) != X2
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k2_relat_1(sK4),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6983])).

cnf(c_6986,plain,
    ( k2_relat_1(sK4) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(k2_relat_1(sK4),k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6984])).

cnf(c_9619,plain,
    ( r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_37702,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_36904,c_106,c_107,c_116,c_590,c_1468,c_1469,c_1587,c_1654,c_1799,c_1800,c_1964,c_2052,c_2602,c_2700,c_3205,c_3206,c_3943,c_3941,c_3944,c_4771,c_4805,c_6986,c_9619,c_36672])).

cnf(c_2051,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
    | sK4 != k1_xboole_0
    | sK1 = k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1427,c_105,c_116])).

cnf(c_2052,plain,
    ( sK3 != k1_xboole_0
    | sK1 = k1_xboole_0
    | sK4 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2051])).

cnf(c_36900,plain,
    ( sK1 = k1_xboole_0
    | sK4 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_36868,c_2052])).

cnf(c_36905,plain,
    ( sK1 = k1_xboole_0
    | sK4 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_36900])).

cnf(c_36906,plain,
    ( sK1 = k1_xboole_0
    | sK4 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_36905,c_6])).

cnf(c_37394,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_36906,c_590,c_1468,c_1469,c_1587,c_1654,c_1799,c_1800,c_1964,c_2052,c_2602,c_2700,c_3205,c_3206,c_3943,c_3941,c_3944,c_4771,c_9619,c_36672])).

cnf(c_18,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1416,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4393,plain,
    ( sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | sK4 = k1_xboole_0
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4324,c_1416])).

cnf(c_2308,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | r1_tarski(sK1,k1_xboole_0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1799,c_1408])).

cnf(c_2594,plain,
    ( ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) != k1_xboole_0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_4641,plain,
    ( sK4 = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4393,c_106,c_107,c_116,c_1488,c_1587,c_1654,c_2308,c_2594,c_3205,c_3206])).

cnf(c_4642,plain,
    ( sK1 != k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4641])).

cnf(c_37512,plain,
    ( sK4 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_37394,c_4642])).

cnf(c_37526,plain,
    ( sK4 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_37512])).

cnf(c_37704,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_37702,c_37526])).

cnf(c_16,plain,
    ( r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1418,plain,
    ( r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2202,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_1418])).

cnf(c_2305,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1422,c_1408])).

cnf(c_2689,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2202,c_2305])).

cnf(c_2783,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2689,c_2202])).

cnf(c_4122,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1421,c_1415])).

cnf(c_13488,plain,
    ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2783,c_4122])).

cnf(c_2534,plain,
    ( m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_1412])).

cnf(c_2834,plain,
    ( r1_tarski(k6_relat_1(k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2534,c_1420])).

cnf(c_3463,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2834,c_2305])).

cnf(c_3469,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3463,c_20])).

cnf(c_13495,plain,
    ( k1_relset_1(X0,X1,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_13488,c_3469])).

cnf(c_37705,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_37704,c_13495])).

cnf(c_37706,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_37705])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:11:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 7.71/1.52  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.71/1.52  
% 7.71/1.52  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.71/1.52  
% 7.71/1.52  ------  iProver source info
% 7.71/1.52  
% 7.71/1.52  git: date: 2020-06-30 10:37:57 +0100
% 7.71/1.52  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.71/1.52  git: non_committed_changes: false
% 7.71/1.52  git: last_make_outside_of_git: false
% 7.71/1.52  
% 7.71/1.52  ------ 
% 7.71/1.52  
% 7.71/1.52  ------ Input Options
% 7.71/1.52  
% 7.71/1.52  --out_options                           all
% 7.71/1.52  --tptp_safe_out                         true
% 7.71/1.52  --problem_path                          ""
% 7.71/1.52  --include_path                          ""
% 7.71/1.52  --clausifier                            res/vclausify_rel
% 7.71/1.52  --clausifier_options                    ""
% 7.71/1.52  --stdin                                 false
% 7.71/1.52  --stats_out                             all
% 7.71/1.52  
% 7.71/1.52  ------ General Options
% 7.71/1.52  
% 7.71/1.52  --fof                                   false
% 7.71/1.52  --time_out_real                         305.
% 7.71/1.52  --time_out_virtual                      -1.
% 7.71/1.52  --symbol_type_check                     false
% 7.71/1.52  --clausify_out                          false
% 7.71/1.52  --sig_cnt_out                           false
% 7.71/1.52  --trig_cnt_out                          false
% 7.71/1.52  --trig_cnt_out_tolerance                1.
% 7.71/1.52  --trig_cnt_out_sk_spl                   false
% 7.71/1.52  --abstr_cl_out                          false
% 7.71/1.52  
% 7.71/1.52  ------ Global Options
% 7.71/1.52  
% 7.71/1.52  --schedule                              default
% 7.71/1.52  --add_important_lit                     false
% 7.71/1.52  --prop_solver_per_cl                    1000
% 7.71/1.52  --min_unsat_core                        false
% 7.71/1.52  --soft_assumptions                      false
% 7.71/1.52  --soft_lemma_size                       3
% 7.71/1.52  --prop_impl_unit_size                   0
% 7.71/1.52  --prop_impl_unit                        []
% 7.71/1.52  --share_sel_clauses                     true
% 7.71/1.52  --reset_solvers                         false
% 7.71/1.52  --bc_imp_inh                            [conj_cone]
% 7.71/1.52  --conj_cone_tolerance                   3.
% 7.71/1.52  --extra_neg_conj                        none
% 7.71/1.52  --large_theory_mode                     true
% 7.71/1.52  --prolific_symb_bound                   200
% 7.71/1.52  --lt_threshold                          2000
% 7.71/1.52  --clause_weak_htbl                      true
% 7.71/1.52  --gc_record_bc_elim                     false
% 7.71/1.52  
% 7.71/1.52  ------ Preprocessing Options
% 7.71/1.52  
% 7.71/1.52  --preprocessing_flag                    true
% 7.71/1.52  --time_out_prep_mult                    0.1
% 7.71/1.52  --splitting_mode                        input
% 7.71/1.52  --splitting_grd                         true
% 7.71/1.52  --splitting_cvd                         false
% 7.71/1.52  --splitting_cvd_svl                     false
% 7.71/1.52  --splitting_nvd                         32
% 7.71/1.52  --sub_typing                            true
% 7.71/1.52  --prep_gs_sim                           true
% 7.71/1.52  --prep_unflatten                        true
% 7.71/1.52  --prep_res_sim                          true
% 7.71/1.52  --prep_upred                            true
% 7.71/1.52  --prep_sem_filter                       exhaustive
% 7.71/1.52  --prep_sem_filter_out                   false
% 7.71/1.52  --pred_elim                             true
% 7.71/1.52  --res_sim_input                         true
% 7.71/1.52  --eq_ax_congr_red                       true
% 7.71/1.52  --pure_diseq_elim                       true
% 7.71/1.52  --brand_transform                       false
% 7.71/1.52  --non_eq_to_eq                          false
% 7.71/1.52  --prep_def_merge                        true
% 7.71/1.52  --prep_def_merge_prop_impl              false
% 7.71/1.52  --prep_def_merge_mbd                    true
% 7.71/1.52  --prep_def_merge_tr_red                 false
% 7.71/1.52  --prep_def_merge_tr_cl                  false
% 7.71/1.52  --smt_preprocessing                     true
% 7.71/1.52  --smt_ac_axioms                         fast
% 7.71/1.52  --preprocessed_out                      false
% 7.71/1.52  --preprocessed_stats                    false
% 7.71/1.52  
% 7.71/1.52  ------ Abstraction refinement Options
% 7.71/1.52  
% 7.71/1.52  --abstr_ref                             []
% 7.71/1.52  --abstr_ref_prep                        false
% 7.71/1.52  --abstr_ref_until_sat                   false
% 7.71/1.52  --abstr_ref_sig_restrict                funpre
% 7.71/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 7.71/1.52  --abstr_ref_under                       []
% 7.71/1.52  
% 7.71/1.52  ------ SAT Options
% 7.71/1.52  
% 7.71/1.52  --sat_mode                              false
% 7.71/1.52  --sat_fm_restart_options                ""
% 7.71/1.52  --sat_gr_def                            false
% 7.71/1.52  --sat_epr_types                         true
% 7.71/1.52  --sat_non_cyclic_types                  false
% 7.71/1.52  --sat_finite_models                     false
% 7.71/1.52  --sat_fm_lemmas                         false
% 7.71/1.52  --sat_fm_prep                           false
% 7.71/1.52  --sat_fm_uc_incr                        true
% 7.71/1.52  --sat_out_model                         small
% 7.71/1.52  --sat_out_clauses                       false
% 7.71/1.52  
% 7.71/1.52  ------ QBF Options
% 7.71/1.52  
% 7.71/1.52  --qbf_mode                              false
% 7.71/1.52  --qbf_elim_univ                         false
% 7.71/1.52  --qbf_dom_inst                          none
% 7.71/1.52  --qbf_dom_pre_inst                      false
% 7.71/1.52  --qbf_sk_in                             false
% 7.71/1.52  --qbf_pred_elim                         true
% 7.71/1.52  --qbf_split                             512
% 7.71/1.52  
% 7.71/1.52  ------ BMC1 Options
% 7.71/1.52  
% 7.71/1.52  --bmc1_incremental                      false
% 7.71/1.52  --bmc1_axioms                           reachable_all
% 7.71/1.52  --bmc1_min_bound                        0
% 7.71/1.52  --bmc1_max_bound                        -1
% 7.71/1.52  --bmc1_max_bound_default                -1
% 7.71/1.52  --bmc1_symbol_reachability              true
% 7.71/1.52  --bmc1_property_lemmas                  false
% 7.71/1.52  --bmc1_k_induction                      false
% 7.71/1.52  --bmc1_non_equiv_states                 false
% 7.71/1.52  --bmc1_deadlock                         false
% 7.71/1.52  --bmc1_ucm                              false
% 7.71/1.52  --bmc1_add_unsat_core                   none
% 7.71/1.52  --bmc1_unsat_core_children              false
% 7.71/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 7.71/1.52  --bmc1_out_stat                         full
% 7.71/1.52  --bmc1_ground_init                      false
% 7.71/1.52  --bmc1_pre_inst_next_state              false
% 7.71/1.52  --bmc1_pre_inst_state                   false
% 7.71/1.52  --bmc1_pre_inst_reach_state             false
% 7.71/1.52  --bmc1_out_unsat_core                   false
% 7.71/1.52  --bmc1_aig_witness_out                  false
% 7.71/1.52  --bmc1_verbose                          false
% 7.71/1.52  --bmc1_dump_clauses_tptp                false
% 7.71/1.52  --bmc1_dump_unsat_core_tptp             false
% 7.71/1.52  --bmc1_dump_file                        -
% 7.71/1.52  --bmc1_ucm_expand_uc_limit              128
% 7.71/1.52  --bmc1_ucm_n_expand_iterations          6
% 7.71/1.52  --bmc1_ucm_extend_mode                  1
% 7.71/1.52  --bmc1_ucm_init_mode                    2
% 7.71/1.52  --bmc1_ucm_cone_mode                    none
% 7.71/1.52  --bmc1_ucm_reduced_relation_type        0
% 7.71/1.52  --bmc1_ucm_relax_model                  4
% 7.71/1.52  --bmc1_ucm_full_tr_after_sat            true
% 7.71/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 7.71/1.52  --bmc1_ucm_layered_model                none
% 7.71/1.52  --bmc1_ucm_max_lemma_size               10
% 7.71/1.52  
% 7.71/1.52  ------ AIG Options
% 7.71/1.52  
% 7.71/1.52  --aig_mode                              false
% 7.71/1.52  
% 7.71/1.52  ------ Instantiation Options
% 7.71/1.52  
% 7.71/1.52  --instantiation_flag                    true
% 7.71/1.52  --inst_sos_flag                         true
% 7.71/1.52  --inst_sos_phase                        true
% 7.71/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.71/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.71/1.52  --inst_lit_sel_side                     num_symb
% 7.71/1.52  --inst_solver_per_active                1400
% 7.71/1.52  --inst_solver_calls_frac                1.
% 7.71/1.52  --inst_passive_queue_type               priority_queues
% 7.71/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.71/1.52  --inst_passive_queues_freq              [25;2]
% 7.71/1.52  --inst_dismatching                      true
% 7.71/1.52  --inst_eager_unprocessed_to_passive     true
% 7.71/1.52  --inst_prop_sim_given                   true
% 7.71/1.52  --inst_prop_sim_new                     false
% 7.71/1.52  --inst_subs_new                         false
% 7.71/1.52  --inst_eq_res_simp                      false
% 7.71/1.52  --inst_subs_given                       false
% 7.71/1.52  --inst_orphan_elimination               true
% 7.71/1.52  --inst_learning_loop_flag               true
% 7.71/1.52  --inst_learning_start                   3000
% 7.71/1.52  --inst_learning_factor                  2
% 7.71/1.52  --inst_start_prop_sim_after_learn       3
% 7.71/1.52  --inst_sel_renew                        solver
% 7.71/1.52  --inst_lit_activity_flag                true
% 7.71/1.52  --inst_restr_to_given                   false
% 7.71/1.52  --inst_activity_threshold               500
% 7.71/1.52  --inst_out_proof                        true
% 7.71/1.52  
% 7.71/1.52  ------ Resolution Options
% 7.71/1.52  
% 7.71/1.52  --resolution_flag                       true
% 7.71/1.52  --res_lit_sel                           adaptive
% 7.71/1.52  --res_lit_sel_side                      none
% 7.71/1.52  --res_ordering                          kbo
% 7.71/1.52  --res_to_prop_solver                    active
% 7.71/1.52  --res_prop_simpl_new                    false
% 7.71/1.52  --res_prop_simpl_given                  true
% 7.71/1.52  --res_passive_queue_type                priority_queues
% 7.71/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.71/1.52  --res_passive_queues_freq               [15;5]
% 7.71/1.52  --res_forward_subs                      full
% 7.71/1.52  --res_backward_subs                     full
% 7.71/1.52  --res_forward_subs_resolution           true
% 7.71/1.52  --res_backward_subs_resolution          true
% 7.71/1.52  --res_orphan_elimination                true
% 7.71/1.52  --res_time_limit                        2.
% 7.71/1.52  --res_out_proof                         true
% 7.71/1.52  
% 7.71/1.52  ------ Superposition Options
% 7.71/1.52  
% 7.71/1.52  --superposition_flag                    true
% 7.71/1.52  --sup_passive_queue_type                priority_queues
% 7.71/1.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.71/1.52  --sup_passive_queues_freq               [8;1;4]
% 7.71/1.52  --demod_completeness_check              fast
% 7.71/1.52  --demod_use_ground                      true
% 7.71/1.52  --sup_to_prop_solver                    passive
% 7.71/1.52  --sup_prop_simpl_new                    true
% 7.71/1.52  --sup_prop_simpl_given                  true
% 7.71/1.52  --sup_fun_splitting                     true
% 7.71/1.52  --sup_smt_interval                      50000
% 7.71/1.52  
% 7.71/1.52  ------ Superposition Simplification Setup
% 7.71/1.52  
% 7.71/1.52  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.71/1.52  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.71/1.52  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.71/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.71/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 7.71/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.71/1.52  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.71/1.52  --sup_immed_triv                        [TrivRules]
% 7.71/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.71/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.71/1.52  --sup_immed_bw_main                     []
% 7.71/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.71/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 7.71/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.71/1.52  --sup_input_bw                          []
% 7.71/1.52  
% 7.71/1.52  ------ Combination Options
% 7.71/1.52  
% 7.71/1.52  --comb_res_mult                         3
% 7.71/1.52  --comb_sup_mult                         2
% 7.71/1.52  --comb_inst_mult                        10
% 7.71/1.52  
% 7.71/1.52  ------ Debug Options
% 7.71/1.52  
% 7.71/1.52  --dbg_backtrace                         false
% 7.71/1.52  --dbg_dump_prop_clauses                 false
% 7.71/1.52  --dbg_dump_prop_clauses_file            -
% 7.71/1.52  --dbg_out_stat                          false
% 7.71/1.52  ------ Parsing...
% 7.71/1.52  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.71/1.52  
% 7.71/1.52  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 7.71/1.52  
% 7.71/1.52  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.71/1.52  
% 7.71/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.71/1.52  ------ Proving...
% 7.71/1.52  ------ Problem Properties 
% 7.71/1.52  
% 7.71/1.52  
% 7.71/1.52  clauses                                 30
% 7.71/1.52  conjectures                             3
% 7.71/1.52  EPR                                     5
% 7.71/1.52  Horn                                    27
% 7.71/1.52  unary                                   10
% 7.71/1.52  binary                                  7
% 7.71/1.52  lits                                    68
% 7.71/1.52  lits eq                                 32
% 7.71/1.52  fd_pure                                 0
% 7.71/1.52  fd_pseudo                               0
% 7.71/1.52  fd_cond                                 4
% 7.71/1.52  fd_pseudo_cond                          1
% 7.71/1.52  AC symbols                              0
% 7.71/1.52  
% 7.71/1.52  ------ Schedule dynamic 5 is on 
% 7.71/1.52  
% 7.71/1.52  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.71/1.52  
% 7.71/1.52  
% 7.71/1.52  ------ 
% 7.71/1.52  Current options:
% 7.71/1.52  ------ 
% 7.71/1.52  
% 7.71/1.52  ------ Input Options
% 7.71/1.52  
% 7.71/1.52  --out_options                           all
% 7.71/1.52  --tptp_safe_out                         true
% 7.71/1.52  --problem_path                          ""
% 7.71/1.52  --include_path                          ""
% 7.71/1.52  --clausifier                            res/vclausify_rel
% 7.71/1.52  --clausifier_options                    ""
% 7.71/1.52  --stdin                                 false
% 7.71/1.52  --stats_out                             all
% 7.71/1.52  
% 7.71/1.52  ------ General Options
% 7.71/1.52  
% 7.71/1.52  --fof                                   false
% 7.71/1.52  --time_out_real                         305.
% 7.71/1.52  --time_out_virtual                      -1.
% 7.71/1.52  --symbol_type_check                     false
% 7.71/1.52  --clausify_out                          false
% 7.71/1.52  --sig_cnt_out                           false
% 7.71/1.52  --trig_cnt_out                          false
% 7.71/1.52  --trig_cnt_out_tolerance                1.
% 7.71/1.52  --trig_cnt_out_sk_spl                   false
% 7.71/1.52  --abstr_cl_out                          false
% 7.71/1.52  
% 7.71/1.52  ------ Global Options
% 7.71/1.52  
% 7.71/1.52  --schedule                              default
% 7.71/1.52  --add_important_lit                     false
% 7.71/1.52  --prop_solver_per_cl                    1000
% 7.71/1.52  --min_unsat_core                        false
% 7.71/1.52  --soft_assumptions                      false
% 7.71/1.52  --soft_lemma_size                       3
% 7.71/1.52  --prop_impl_unit_size                   0
% 7.71/1.52  --prop_impl_unit                        []
% 7.71/1.52  --share_sel_clauses                     true
% 7.71/1.52  --reset_solvers                         false
% 7.71/1.52  --bc_imp_inh                            [conj_cone]
% 7.71/1.52  --conj_cone_tolerance                   3.
% 7.71/1.52  --extra_neg_conj                        none
% 7.71/1.52  --large_theory_mode                     true
% 7.71/1.52  --prolific_symb_bound                   200
% 7.71/1.52  --lt_threshold                          2000
% 7.71/1.52  --clause_weak_htbl                      true
% 7.71/1.52  --gc_record_bc_elim                     false
% 7.71/1.52  
% 7.71/1.52  ------ Preprocessing Options
% 7.71/1.52  
% 7.71/1.52  --preprocessing_flag                    true
% 7.71/1.52  --time_out_prep_mult                    0.1
% 7.71/1.52  --splitting_mode                        input
% 7.71/1.52  --splitting_grd                         true
% 7.71/1.52  --splitting_cvd                         false
% 7.71/1.52  --splitting_cvd_svl                     false
% 7.71/1.52  --splitting_nvd                         32
% 7.71/1.52  --sub_typing                            true
% 7.71/1.52  --prep_gs_sim                           true
% 7.71/1.52  --prep_unflatten                        true
% 7.71/1.52  --prep_res_sim                          true
% 7.71/1.52  --prep_upred                            true
% 7.71/1.52  --prep_sem_filter                       exhaustive
% 7.71/1.52  --prep_sem_filter_out                   false
% 7.71/1.52  --pred_elim                             true
% 7.71/1.52  --res_sim_input                         true
% 7.71/1.52  --eq_ax_congr_red                       true
% 7.71/1.52  --pure_diseq_elim                       true
% 7.71/1.52  --brand_transform                       false
% 7.71/1.52  --non_eq_to_eq                          false
% 7.71/1.52  --prep_def_merge                        true
% 7.71/1.52  --prep_def_merge_prop_impl              false
% 7.71/1.52  --prep_def_merge_mbd                    true
% 7.71/1.52  --prep_def_merge_tr_red                 false
% 7.71/1.52  --prep_def_merge_tr_cl                  false
% 7.71/1.52  --smt_preprocessing                     true
% 7.71/1.52  --smt_ac_axioms                         fast
% 7.71/1.52  --preprocessed_out                      false
% 7.71/1.52  --preprocessed_stats                    false
% 7.71/1.52  
% 7.71/1.52  ------ Abstraction refinement Options
% 7.71/1.52  
% 7.71/1.52  --abstr_ref                             []
% 7.71/1.52  --abstr_ref_prep                        false
% 7.71/1.52  --abstr_ref_until_sat                   false
% 7.71/1.52  --abstr_ref_sig_restrict                funpre
% 7.71/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 7.71/1.52  --abstr_ref_under                       []
% 7.71/1.52  
% 7.71/1.52  ------ SAT Options
% 7.71/1.52  
% 7.71/1.52  --sat_mode                              false
% 7.71/1.52  --sat_fm_restart_options                ""
% 7.71/1.52  --sat_gr_def                            false
% 7.71/1.52  --sat_epr_types                         true
% 7.71/1.52  --sat_non_cyclic_types                  false
% 7.71/1.52  --sat_finite_models                     false
% 7.71/1.52  --sat_fm_lemmas                         false
% 7.71/1.52  --sat_fm_prep                           false
% 7.71/1.52  --sat_fm_uc_incr                        true
% 7.71/1.52  --sat_out_model                         small
% 7.71/1.52  --sat_out_clauses                       false
% 7.71/1.52  
% 7.71/1.52  ------ QBF Options
% 7.71/1.52  
% 7.71/1.52  --qbf_mode                              false
% 7.71/1.52  --qbf_elim_univ                         false
% 7.71/1.52  --qbf_dom_inst                          none
% 7.71/1.52  --qbf_dom_pre_inst                      false
% 7.71/1.52  --qbf_sk_in                             false
% 7.71/1.52  --qbf_pred_elim                         true
% 7.71/1.52  --qbf_split                             512
% 7.71/1.52  
% 7.71/1.52  ------ BMC1 Options
% 7.71/1.52  
% 7.71/1.52  --bmc1_incremental                      false
% 7.71/1.52  --bmc1_axioms                           reachable_all
% 7.71/1.52  --bmc1_min_bound                        0
% 7.71/1.52  --bmc1_max_bound                        -1
% 7.71/1.52  --bmc1_max_bound_default                -1
% 7.71/1.52  --bmc1_symbol_reachability              true
% 7.71/1.52  --bmc1_property_lemmas                  false
% 7.71/1.52  --bmc1_k_induction                      false
% 7.71/1.52  --bmc1_non_equiv_states                 false
% 7.71/1.52  --bmc1_deadlock                         false
% 7.71/1.52  --bmc1_ucm                              false
% 7.71/1.52  --bmc1_add_unsat_core                   none
% 7.71/1.52  --bmc1_unsat_core_children              false
% 7.71/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 7.71/1.52  --bmc1_out_stat                         full
% 7.71/1.52  --bmc1_ground_init                      false
% 7.71/1.52  --bmc1_pre_inst_next_state              false
% 7.71/1.52  --bmc1_pre_inst_state                   false
% 7.71/1.52  --bmc1_pre_inst_reach_state             false
% 7.71/1.52  --bmc1_out_unsat_core                   false
% 7.71/1.52  --bmc1_aig_witness_out                  false
% 7.71/1.52  --bmc1_verbose                          false
% 7.71/1.52  --bmc1_dump_clauses_tptp                false
% 7.71/1.52  --bmc1_dump_unsat_core_tptp             false
% 7.71/1.52  --bmc1_dump_file                        -
% 7.71/1.52  --bmc1_ucm_expand_uc_limit              128
% 7.71/1.52  --bmc1_ucm_n_expand_iterations          6
% 7.71/1.52  --bmc1_ucm_extend_mode                  1
% 7.71/1.52  --bmc1_ucm_init_mode                    2
% 7.71/1.52  --bmc1_ucm_cone_mode                    none
% 7.71/1.52  --bmc1_ucm_reduced_relation_type        0
% 7.71/1.52  --bmc1_ucm_relax_model                  4
% 7.71/1.52  --bmc1_ucm_full_tr_after_sat            true
% 7.71/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 7.71/1.52  --bmc1_ucm_layered_model                none
% 7.71/1.52  --bmc1_ucm_max_lemma_size               10
% 7.71/1.52  
% 7.71/1.52  ------ AIG Options
% 7.71/1.52  
% 7.71/1.52  --aig_mode                              false
% 7.71/1.52  
% 7.71/1.52  ------ Instantiation Options
% 7.71/1.52  
% 7.71/1.52  --instantiation_flag                    true
% 7.71/1.52  --inst_sos_flag                         true
% 7.71/1.52  --inst_sos_phase                        true
% 7.71/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.71/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.71/1.52  --inst_lit_sel_side                     none
% 7.71/1.52  --inst_solver_per_active                1400
% 7.71/1.52  --inst_solver_calls_frac                1.
% 7.71/1.52  --inst_passive_queue_type               priority_queues
% 7.71/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.71/1.52  --inst_passive_queues_freq              [25;2]
% 7.71/1.52  --inst_dismatching                      true
% 7.71/1.52  --inst_eager_unprocessed_to_passive     true
% 7.71/1.52  --inst_prop_sim_given                   true
% 7.71/1.52  --inst_prop_sim_new                     false
% 7.71/1.52  --inst_subs_new                         false
% 7.71/1.52  --inst_eq_res_simp                      false
% 7.71/1.52  --inst_subs_given                       false
% 7.71/1.52  --inst_orphan_elimination               true
% 7.71/1.52  --inst_learning_loop_flag               true
% 7.71/1.52  --inst_learning_start                   3000
% 7.71/1.52  --inst_learning_factor                  2
% 7.71/1.52  --inst_start_prop_sim_after_learn       3
% 7.71/1.52  --inst_sel_renew                        solver
% 7.71/1.52  --inst_lit_activity_flag                true
% 7.71/1.52  --inst_restr_to_given                   false
% 7.71/1.52  --inst_activity_threshold               500
% 7.71/1.52  --inst_out_proof                        true
% 7.71/1.52  
% 7.71/1.52  ------ Resolution Options
% 7.71/1.52  
% 7.71/1.52  --resolution_flag                       false
% 7.71/1.52  --res_lit_sel                           adaptive
% 7.71/1.52  --res_lit_sel_side                      none
% 7.71/1.52  --res_ordering                          kbo
% 7.71/1.52  --res_to_prop_solver                    active
% 7.71/1.52  --res_prop_simpl_new                    false
% 7.71/1.52  --res_prop_simpl_given                  true
% 7.71/1.52  --res_passive_queue_type                priority_queues
% 7.71/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.71/1.52  --res_passive_queues_freq               [15;5]
% 7.71/1.52  --res_forward_subs                      full
% 7.71/1.52  --res_backward_subs                     full
% 7.71/1.52  --res_forward_subs_resolution           true
% 7.71/1.52  --res_backward_subs_resolution          true
% 7.71/1.52  --res_orphan_elimination                true
% 7.71/1.52  --res_time_limit                        2.
% 7.71/1.52  --res_out_proof                         true
% 7.71/1.52  
% 7.71/1.52  ------ Superposition Options
% 7.71/1.52  
% 7.71/1.52  --superposition_flag                    true
% 7.71/1.52  --sup_passive_queue_type                priority_queues
% 7.71/1.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.71/1.52  --sup_passive_queues_freq               [8;1;4]
% 7.71/1.52  --demod_completeness_check              fast
% 7.71/1.52  --demod_use_ground                      true
% 7.71/1.52  --sup_to_prop_solver                    passive
% 7.71/1.52  --sup_prop_simpl_new                    true
% 7.71/1.52  --sup_prop_simpl_given                  true
% 7.71/1.52  --sup_fun_splitting                     true
% 7.71/1.52  --sup_smt_interval                      50000
% 7.71/1.52  
% 7.71/1.52  ------ Superposition Simplification Setup
% 7.71/1.52  
% 7.71/1.52  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.71/1.52  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.71/1.52  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.71/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.71/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 7.71/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.71/1.52  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.71/1.52  --sup_immed_triv                        [TrivRules]
% 7.71/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.71/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.71/1.52  --sup_immed_bw_main                     []
% 7.71/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.71/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 7.71/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.71/1.52  --sup_input_bw                          []
% 7.71/1.52  
% 7.71/1.52  ------ Combination Options
% 7.71/1.52  
% 7.71/1.52  --comb_res_mult                         3
% 7.71/1.52  --comb_sup_mult                         2
% 7.71/1.52  --comb_inst_mult                        10
% 7.71/1.52  
% 7.71/1.52  ------ Debug Options
% 7.71/1.52  
% 7.71/1.52  --dbg_backtrace                         false
% 7.71/1.52  --dbg_dump_prop_clauses                 false
% 7.71/1.52  --dbg_dump_prop_clauses_file            -
% 7.71/1.52  --dbg_out_stat                          false
% 7.71/1.52  
% 7.71/1.52  
% 7.71/1.52  
% 7.71/1.52  
% 7.71/1.52  ------ Proving...
% 7.71/1.52  
% 7.71/1.52  
% 7.71/1.52  % SZS status Theorem for theBenchmark.p
% 7.71/1.52  
% 7.71/1.52   Resolution empty clause
% 7.71/1.52  
% 7.71/1.52  % SZS output start CNFRefutation for theBenchmark.p
% 7.71/1.52  
% 7.71/1.52  fof(f2,axiom,(
% 7.71/1.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.71/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.52  
% 7.71/1.52  fof(f42,plain,(
% 7.71/1.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.71/1.52    inference(nnf_transformation,[],[f2])).
% 7.71/1.52  
% 7.71/1.52  fof(f43,plain,(
% 7.71/1.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.71/1.52    inference(flattening,[],[f42])).
% 7.71/1.52  
% 7.71/1.52  fof(f52,plain,(
% 7.71/1.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.71/1.52    inference(cnf_transformation,[],[f43])).
% 7.71/1.52  
% 7.71/1.52  fof(f90,plain,(
% 7.71/1.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.71/1.52    inference(equality_resolution,[],[f52])).
% 7.71/1.52  
% 7.71/1.52  fof(f20,conjecture,(
% 7.71/1.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 7.71/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.52  
% 7.71/1.52  fof(f21,negated_conjecture,(
% 7.71/1.52    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 7.71/1.52    inference(negated_conjecture,[],[f20])).
% 7.71/1.52  
% 7.71/1.52  fof(f38,plain,(
% 7.71/1.52    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(k2_relset_1(X0,X1,X3),X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 7.71/1.52    inference(ennf_transformation,[],[f21])).
% 7.71/1.52  
% 7.71/1.52  fof(f39,plain,(
% 7.71/1.52    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 7.71/1.52    inference(flattening,[],[f38])).
% 7.71/1.52  
% 7.71/1.52  fof(f49,plain,(
% 7.71/1.52    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) | ~v1_funct_2(sK4,sK1,sK3) | ~v1_funct_1(sK4)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4))),
% 7.71/1.52    introduced(choice_axiom,[])).
% 7.71/1.52  
% 7.71/1.52  fof(f50,plain,(
% 7.71/1.52    (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) | ~v1_funct_2(sK4,sK1,sK3) | ~v1_funct_1(sK4)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)),
% 7.71/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f39,f49])).
% 7.71/1.52  
% 7.71/1.52  fof(f85,plain,(
% 7.71/1.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 7.71/1.52    inference(cnf_transformation,[],[f50])).
% 7.71/1.52  
% 7.71/1.52  fof(f16,axiom,(
% 7.71/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 7.71/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.52  
% 7.71/1.52  fof(f33,plain,(
% 7.71/1.52    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.71/1.52    inference(ennf_transformation,[],[f16])).
% 7.71/1.52  
% 7.71/1.52  fof(f74,plain,(
% 7.71/1.52    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.71/1.52    inference(cnf_transformation,[],[f33])).
% 7.71/1.52  
% 7.71/1.52  fof(f86,plain,(
% 7.71/1.52    r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3)),
% 7.71/1.52    inference(cnf_transformation,[],[f50])).
% 7.71/1.52  
% 7.71/1.52  fof(f17,axiom,(
% 7.71/1.52    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.71/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.52  
% 7.71/1.52  fof(f34,plain,(
% 7.71/1.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 7.71/1.52    inference(ennf_transformation,[],[f17])).
% 7.71/1.52  
% 7.71/1.52  fof(f35,plain,(
% 7.71/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 7.71/1.52    inference(flattening,[],[f34])).
% 7.71/1.52  
% 7.71/1.52  fof(f75,plain,(
% 7.71/1.52    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 7.71/1.52    inference(cnf_transformation,[],[f35])).
% 7.71/1.52  
% 7.71/1.52  fof(f15,axiom,(
% 7.71/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.71/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.52  
% 7.71/1.52  fof(f32,plain,(
% 7.71/1.52    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.71/1.52    inference(ennf_transformation,[],[f15])).
% 7.71/1.52  
% 7.71/1.52  fof(f73,plain,(
% 7.71/1.52    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.71/1.52    inference(cnf_transformation,[],[f32])).
% 7.71/1.52  
% 7.71/1.52  fof(f10,axiom,(
% 7.71/1.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.71/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.52  
% 7.71/1.52  fof(f66,plain,(
% 7.71/1.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.71/1.52    inference(cnf_transformation,[],[f10])).
% 7.71/1.52  
% 7.71/1.52  fof(f18,axiom,(
% 7.71/1.52    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 7.71/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.52  
% 7.71/1.52  fof(f76,plain,(
% 7.71/1.52    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.71/1.52    inference(cnf_transformation,[],[f18])).
% 7.71/1.52  
% 7.71/1.52  fof(f6,axiom,(
% 7.71/1.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.71/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.52  
% 7.71/1.52  fof(f46,plain,(
% 7.71/1.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.71/1.52    inference(nnf_transformation,[],[f6])).
% 7.71/1.52  
% 7.71/1.52  fof(f60,plain,(
% 7.71/1.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.71/1.52    inference(cnf_transformation,[],[f46])).
% 7.71/1.52  
% 7.71/1.52  fof(f8,axiom,(
% 7.71/1.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.71/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.52  
% 7.71/1.52  fof(f27,plain,(
% 7.71/1.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.71/1.52    inference(ennf_transformation,[],[f8])).
% 7.71/1.52  
% 7.71/1.52  fof(f63,plain,(
% 7.71/1.52    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.71/1.52    inference(cnf_transformation,[],[f27])).
% 7.71/1.52  
% 7.71/1.52  fof(f61,plain,(
% 7.71/1.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.71/1.52    inference(cnf_transformation,[],[f46])).
% 7.71/1.52  
% 7.71/1.52  fof(f14,axiom,(
% 7.71/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.71/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.52  
% 7.71/1.52  fof(f22,plain,(
% 7.71/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.71/1.52    inference(pure_predicate_removal,[],[f14])).
% 7.71/1.52  
% 7.71/1.52  fof(f31,plain,(
% 7.71/1.52    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.71/1.52    inference(ennf_transformation,[],[f22])).
% 7.71/1.52  
% 7.71/1.52  fof(f72,plain,(
% 7.71/1.52    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.71/1.52    inference(cnf_transformation,[],[f31])).
% 7.71/1.52  
% 7.71/1.52  fof(f9,axiom,(
% 7.71/1.52    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 7.71/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.52  
% 7.71/1.52  fof(f28,plain,(
% 7.71/1.52    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.71/1.52    inference(ennf_transformation,[],[f9])).
% 7.71/1.52  
% 7.71/1.52  fof(f47,plain,(
% 7.71/1.52    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.71/1.52    inference(nnf_transformation,[],[f28])).
% 7.71/1.52  
% 7.71/1.52  fof(f64,plain,(
% 7.71/1.52    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.71/1.52    inference(cnf_transformation,[],[f47])).
% 7.71/1.52  
% 7.71/1.52  fof(f13,axiom,(
% 7.71/1.52    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 7.71/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.52  
% 7.71/1.52  fof(f71,plain,(
% 7.71/1.52    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 7.71/1.52    inference(cnf_transformation,[],[f13])).
% 7.71/1.52  
% 7.71/1.52  fof(f5,axiom,(
% 7.71/1.52    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.71/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.52  
% 7.71/1.52  fof(f44,plain,(
% 7.71/1.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.71/1.52    inference(nnf_transformation,[],[f5])).
% 7.71/1.52  
% 7.71/1.52  fof(f45,plain,(
% 7.71/1.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.71/1.52    inference(flattening,[],[f44])).
% 7.71/1.52  
% 7.71/1.52  fof(f59,plain,(
% 7.71/1.52    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 7.71/1.52    inference(cnf_transformation,[],[f45])).
% 7.71/1.52  
% 7.71/1.52  fof(f91,plain,(
% 7.71/1.52    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 7.71/1.52    inference(equality_resolution,[],[f59])).
% 7.71/1.52  
% 7.71/1.52  fof(f70,plain,(
% 7.71/1.52    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 7.71/1.52    inference(cnf_transformation,[],[f13])).
% 7.71/1.52  
% 7.71/1.52  fof(f54,plain,(
% 7.71/1.52    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.71/1.52    inference(cnf_transformation,[],[f43])).
% 7.71/1.52  
% 7.71/1.52  fof(f58,plain,(
% 7.71/1.52    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 7.71/1.52    inference(cnf_transformation,[],[f45])).
% 7.71/1.52  
% 7.71/1.52  fof(f92,plain,(
% 7.71/1.52    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 7.71/1.52    inference(equality_resolution,[],[f58])).
% 7.71/1.52  
% 7.71/1.52  fof(f57,plain,(
% 7.71/1.52    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 7.71/1.52    inference(cnf_transformation,[],[f45])).
% 7.71/1.52  
% 7.71/1.52  fof(f19,axiom,(
% 7.71/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.71/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.52  
% 7.71/1.52  fof(f36,plain,(
% 7.71/1.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.71/1.52    inference(ennf_transformation,[],[f19])).
% 7.71/1.52  
% 7.71/1.52  fof(f37,plain,(
% 7.71/1.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.71/1.52    inference(flattening,[],[f36])).
% 7.71/1.52  
% 7.71/1.52  fof(f48,plain,(
% 7.71/1.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.71/1.52    inference(nnf_transformation,[],[f37])).
% 7.71/1.52  
% 7.71/1.52  fof(f81,plain,(
% 7.71/1.52    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.71/1.52    inference(cnf_transformation,[],[f48])).
% 7.71/1.52  
% 7.71/1.52  fof(f95,plain,(
% 7.71/1.52    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 7.71/1.52    inference(equality_resolution,[],[f81])).
% 7.71/1.52  
% 7.71/1.52  fof(f84,plain,(
% 7.71/1.52    v1_funct_2(sK4,sK1,sK2)),
% 7.71/1.52    inference(cnf_transformation,[],[f50])).
% 7.71/1.52  
% 7.71/1.52  fof(f87,plain,(
% 7.71/1.52    k1_xboole_0 = sK1 | k1_xboole_0 != sK2),
% 7.71/1.52    inference(cnf_transformation,[],[f50])).
% 7.71/1.52  
% 7.71/1.52  fof(f77,plain,(
% 7.71/1.52    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.71/1.52    inference(cnf_transformation,[],[f48])).
% 7.71/1.52  
% 7.71/1.52  fof(f79,plain,(
% 7.71/1.52    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.71/1.52    inference(cnf_transformation,[],[f48])).
% 7.71/1.52  
% 7.71/1.52  fof(f88,plain,(
% 7.71/1.52    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) | ~v1_funct_2(sK4,sK1,sK3) | ~v1_funct_1(sK4)),
% 7.71/1.52    inference(cnf_transformation,[],[f50])).
% 7.71/1.52  
% 7.71/1.52  fof(f83,plain,(
% 7.71/1.52    v1_funct_1(sK4)),
% 7.71/1.52    inference(cnf_transformation,[],[f50])).
% 7.71/1.52  
% 7.71/1.52  fof(f80,plain,(
% 7.71/1.52    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.71/1.52    inference(cnf_transformation,[],[f48])).
% 7.71/1.52  
% 7.71/1.52  fof(f96,plain,(
% 7.71/1.52    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 7.71/1.52    inference(equality_resolution,[],[f80])).
% 7.71/1.52  
% 7.71/1.52  fof(f82,plain,(
% 7.71/1.52    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.71/1.52    inference(cnf_transformation,[],[f48])).
% 7.71/1.52  
% 7.71/1.52  fof(f93,plain,(
% 7.71/1.52    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.71/1.52    inference(equality_resolution,[],[f82])).
% 7.71/1.52  
% 7.71/1.52  fof(f94,plain,(
% 7.71/1.52    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 7.71/1.52    inference(equality_resolution,[],[f93])).
% 7.71/1.52  
% 7.71/1.52  fof(f12,axiom,(
% 7.71/1.52    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 7.71/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.52  
% 7.71/1.52  fof(f29,plain,(
% 7.71/1.52    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 7.71/1.52    inference(ennf_transformation,[],[f12])).
% 7.71/1.52  
% 7.71/1.52  fof(f30,plain,(
% 7.71/1.52    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 7.71/1.52    inference(flattening,[],[f29])).
% 7.71/1.52  
% 7.71/1.52  fof(f69,plain,(
% 7.71/1.52    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.71/1.52    inference(cnf_transformation,[],[f30])).
% 7.71/1.52  
% 7.71/1.52  fof(f1,axiom,(
% 7.71/1.52    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 7.71/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.52  
% 7.71/1.52  fof(f23,plain,(
% 7.71/1.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 7.71/1.52    inference(ennf_transformation,[],[f1])).
% 7.71/1.52  
% 7.71/1.52  fof(f40,plain,(
% 7.71/1.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 7.71/1.52    introduced(choice_axiom,[])).
% 7.71/1.52  
% 7.71/1.52  fof(f41,plain,(
% 7.71/1.52    ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0)),
% 7.71/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f40])).
% 7.71/1.52  
% 7.71/1.52  fof(f51,plain,(
% 7.71/1.52    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 7.71/1.52    inference(cnf_transformation,[],[f41])).
% 7.71/1.52  
% 7.71/1.52  fof(f7,axiom,(
% 7.71/1.52    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 7.71/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.52  
% 7.71/1.52  fof(f26,plain,(
% 7.71/1.52    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 7.71/1.52    inference(ennf_transformation,[],[f7])).
% 7.71/1.52  
% 7.71/1.52  fof(f62,plain,(
% 7.71/1.52    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 7.71/1.52    inference(cnf_transformation,[],[f26])).
% 7.71/1.52  
% 7.71/1.52  fof(f3,axiom,(
% 7.71/1.52    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 7.71/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.52  
% 7.71/1.52  fof(f55,plain,(
% 7.71/1.52    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 7.71/1.52    inference(cnf_transformation,[],[f3])).
% 7.71/1.52  
% 7.71/1.52  fof(f4,axiom,(
% 7.71/1.52    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 7.71/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.52  
% 7.71/1.52  fof(f24,plain,(
% 7.71/1.52    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 7.71/1.52    inference(ennf_transformation,[],[f4])).
% 7.71/1.52  
% 7.71/1.52  fof(f25,plain,(
% 7.71/1.52    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 7.71/1.52    inference(flattening,[],[f24])).
% 7.71/1.52  
% 7.71/1.52  fof(f56,plain,(
% 7.71/1.52    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 7.71/1.52    inference(cnf_transformation,[],[f25])).
% 7.71/1.52  
% 7.71/1.52  fof(f68,plain,(
% 7.71/1.52    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.71/1.52    inference(cnf_transformation,[],[f30])).
% 7.71/1.52  
% 7.71/1.52  fof(f11,axiom,(
% 7.71/1.52    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1)),
% 7.71/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.52  
% 7.71/1.52  fof(f67,plain,(
% 7.71/1.52    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1)) )),
% 7.71/1.52    inference(cnf_transformation,[],[f11])).
% 7.71/1.52  
% 7.71/1.52  cnf(c_3,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f90]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_1422,plain,
% 7.71/1.52      ( r1_tarski(X0,X0) = iProver_top ),
% 7.71/1.52      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_35,negated_conjecture,
% 7.71/1.52      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 7.71/1.52      inference(cnf_transformation,[],[f85]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_1410,plain,
% 7.71/1.52      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 7.71/1.52      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_23,plain,
% 7.71/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.71/1.52      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.71/1.52      inference(cnf_transformation,[],[f74]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_1414,plain,
% 7.71/1.52      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.71/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.71/1.52      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_3776,plain,
% 7.71/1.52      ( k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4) ),
% 7.71/1.52      inference(superposition,[status(thm)],[c_1410,c_1414]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_34,negated_conjecture,
% 7.71/1.52      ( r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) ),
% 7.71/1.52      inference(cnf_transformation,[],[f86]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_1411,plain,
% 7.71/1.52      ( r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) = iProver_top ),
% 7.71/1.52      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_3941,plain,
% 7.71/1.52      ( r1_tarski(k2_relat_1(sK4),sK3) = iProver_top ),
% 7.71/1.52      inference(demodulation,[status(thm)],[c_3776,c_1411]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_24,plain,
% 7.71/1.52      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.71/1.52      | ~ r1_tarski(k2_relat_1(X0),X2)
% 7.71/1.52      | ~ r1_tarski(k1_relat_1(X0),X1)
% 7.71/1.52      | ~ v1_relat_1(X0) ),
% 7.71/1.52      inference(cnf_transformation,[],[f75]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_1413,plain,
% 7.71/1.52      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 7.71/1.52      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 7.71/1.52      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 7.71/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.71/1.52      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_22,plain,
% 7.71/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.71/1.52      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.71/1.52      inference(cnf_transformation,[],[f73]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_1415,plain,
% 7.71/1.52      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.71/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.71/1.52      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_4123,plain,
% 7.71/1.52      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.71/1.52      | r1_tarski(k2_relat_1(X2),X1) != iProver_top
% 7.71/1.52      | r1_tarski(k1_relat_1(X2),X0) != iProver_top
% 7.71/1.52      | v1_relat_1(X2) != iProver_top ),
% 7.71/1.52      inference(superposition,[status(thm)],[c_1413,c_1415]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_35231,plain,
% 7.71/1.52      ( k1_relset_1(X0,sK3,sK4) = k1_relat_1(sK4)
% 7.71/1.52      | r1_tarski(k1_relat_1(sK4),X0) != iProver_top
% 7.71/1.52      | v1_relat_1(sK4) != iProver_top ),
% 7.71/1.52      inference(superposition,[status(thm)],[c_3941,c_4123]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_15,plain,
% 7.71/1.52      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.71/1.52      inference(cnf_transformation,[],[f66]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_1419,plain,
% 7.71/1.52      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 7.71/1.52      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_25,plain,
% 7.71/1.52      ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 7.71/1.52      inference(cnf_transformation,[],[f76]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_1412,plain,
% 7.71/1.52      ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 7.71/1.52      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_10,plain,
% 7.71/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.71/1.52      inference(cnf_transformation,[],[f60]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_1420,plain,
% 7.71/1.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.71/1.52      | r1_tarski(X0,X1) = iProver_top ),
% 7.71/1.52      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_2832,plain,
% 7.71/1.52      ( r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0)) = iProver_top ),
% 7.71/1.52      inference(superposition,[status(thm)],[c_1412,c_1420]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_12,plain,
% 7.71/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 7.71/1.52      inference(cnf_transformation,[],[f63]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_9,plain,
% 7.71/1.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.71/1.52      inference(cnf_transformation,[],[f61]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_264,plain,
% 7.71/1.52      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.71/1.52      inference(prop_impl,[status(thm)],[c_9]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_265,plain,
% 7.71/1.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.71/1.52      inference(renaming,[status(thm)],[c_264]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_328,plain,
% 7.71/1.52      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 7.71/1.52      inference(bin_hyper_res,[status(thm)],[c_12,c_265]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_1409,plain,
% 7.71/1.52      ( r1_tarski(X0,X1) != iProver_top
% 7.71/1.52      | v1_relat_1(X1) != iProver_top
% 7.71/1.52      | v1_relat_1(X0) = iProver_top ),
% 7.71/1.52      inference(predicate_to_equality,[status(thm)],[c_328]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_6895,plain,
% 7.71/1.52      ( v1_relat_1(k2_zfmisc_1(X0,X0)) != iProver_top
% 7.71/1.52      | v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 7.71/1.52      inference(superposition,[status(thm)],[c_2832,c_1409]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_17992,plain,
% 7.71/1.52      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 7.71/1.52      inference(superposition,[status(thm)],[c_1419,c_6895]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_21,plain,
% 7.71/1.52      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.71/1.52      inference(cnf_transformation,[],[f72]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_14,plain,
% 7.71/1.52      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 7.71/1.52      inference(cnf_transformation,[],[f64]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_490,plain,
% 7.71/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.71/1.52      | r1_tarski(k1_relat_1(X0),X1)
% 7.71/1.52      | ~ v1_relat_1(X0) ),
% 7.71/1.52      inference(resolution,[status(thm)],[c_21,c_14]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_1407,plain,
% 7.71/1.52      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.71/1.52      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 7.71/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.71/1.52      inference(predicate_to_equality,[status(thm)],[c_490]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_1799,plain,
% 7.71/1.52      ( r1_tarski(k1_relat_1(sK4),sK1) = iProver_top
% 7.71/1.52      | v1_relat_1(sK4) != iProver_top ),
% 7.71/1.52      inference(superposition,[status(thm)],[c_1410,c_1407]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_19,plain,
% 7.71/1.52      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 7.71/1.52      inference(cnf_transformation,[],[f71]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_6,plain,
% 7.71/1.52      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.71/1.52      inference(cnf_transformation,[],[f91]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_3523,plain,
% 7.71/1.52      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top
% 7.71/1.52      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 7.71/1.52      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 7.71/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.71/1.52      inference(superposition,[status(thm)],[c_1413,c_1420]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_10898,plain,
% 7.71/1.52      ( r1_tarski(X0,k1_xboole_0) = iProver_top
% 7.71/1.52      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 7.71/1.52      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 7.71/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.71/1.52      inference(superposition,[status(thm)],[c_6,c_3523]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_1801,plain,
% 7.71/1.52      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.71/1.52      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 7.71/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.71/1.52      inference(superposition,[status(thm)],[c_6,c_1407]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_3521,plain,
% 7.71/1.52      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 7.71/1.52      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 7.71/1.52      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 7.71/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.71/1.52      inference(superposition,[status(thm)],[c_6,c_1413]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_4804,plain,
% 7.71/1.52      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 7.71/1.52      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 7.71/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.71/1.52      inference(superposition,[status(thm)],[c_1422,c_3521]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_11145,plain,
% 7.71/1.52      ( r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 7.71/1.52      | r1_tarski(X0,k1_xboole_0) = iProver_top
% 7.71/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.71/1.52      inference(global_propositional_subsumption,
% 7.71/1.52                [status(thm)],
% 7.71/1.52                [c_10898,c_1801,c_4804]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_11146,plain,
% 7.71/1.52      ( r1_tarski(X0,k1_xboole_0) = iProver_top
% 7.71/1.52      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 7.71/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.71/1.52      inference(renaming,[status(thm)],[c_11145]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_11150,plain,
% 7.71/1.52      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 7.71/1.52      | r1_tarski(k6_relat_1(X0),k1_xboole_0) = iProver_top
% 7.71/1.52      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 7.71/1.52      inference(superposition,[status(thm)],[c_19,c_11146]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_20,plain,
% 7.71/1.52      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 7.71/1.52      inference(cnf_transformation,[],[f70]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_1421,plain,
% 7.71/1.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.71/1.52      | r1_tarski(X0,X1) != iProver_top ),
% 7.71/1.52      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_4679,plain,
% 7.71/1.52      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 7.71/1.52      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 7.71/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.71/1.52      inference(superposition,[status(thm)],[c_1421,c_1801]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_1,plain,
% 7.71/1.52      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.71/1.52      inference(cnf_transformation,[],[f54]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_1423,plain,
% 7.71/1.52      ( X0 = X1
% 7.71/1.52      | r1_tarski(X0,X1) != iProver_top
% 7.71/1.52      | r1_tarski(X1,X0) != iProver_top ),
% 7.71/1.52      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_15277,plain,
% 7.71/1.52      ( k1_relat_1(X0) = X1
% 7.71/1.52      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 7.71/1.52      | r1_tarski(X0,k1_xboole_0) != iProver_top
% 7.71/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.71/1.52      inference(superposition,[status(thm)],[c_4679,c_1423]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_7,plain,
% 7.71/1.52      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.71/1.52      inference(cnf_transformation,[],[f92]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_2948,plain,
% 7.71/1.52      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 7.71/1.52      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 7.71/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.71/1.52      inference(superposition,[status(thm)],[c_1421,c_1407]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_8476,plain,
% 7.71/1.52      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 7.71/1.52      | r1_tarski(k1_relat_1(X0),k1_xboole_0) = iProver_top
% 7.71/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.71/1.52      inference(superposition,[status(thm)],[c_7,c_2948]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_8492,plain,
% 7.71/1.52      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 7.71/1.52      | v1_relat_1(X0) != iProver_top
% 7.71/1.52      | v1_relat_1(k1_relat_1(X0)) = iProver_top
% 7.71/1.52      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.71/1.52      inference(superposition,[status(thm)],[c_8476,c_1409]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_87,plain,
% 7.71/1.52      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 7.71/1.52      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_89,plain,
% 7.71/1.52      ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 7.71/1.52      inference(instantiation,[status(thm)],[c_87]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_8,plain,
% 7.71/1.52      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 7.71/1.52      | k1_xboole_0 = X0
% 7.71/1.52      | k1_xboole_0 = X1 ),
% 7.71/1.52      inference(cnf_transformation,[],[f57]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_106,plain,
% 7.71/1.52      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 7.71/1.52      | k1_xboole_0 = k1_xboole_0 ),
% 7.71/1.52      inference(instantiation,[status(thm)],[c_8]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_107,plain,
% 7.71/1.52      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 7.71/1.52      inference(instantiation,[status(thm)],[c_7]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_114,plain,
% 7.71/1.52      ( r1_tarski(X0,X0) = iProver_top ),
% 7.71/1.52      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_116,plain,
% 7.71/1.52      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 7.71/1.52      inference(instantiation,[status(thm)],[c_114]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_1594,plain,
% 7.71/1.52      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 7.71/1.52      | v1_relat_1(X0)
% 7.71/1.52      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 7.71/1.52      inference(instantiation,[status(thm)],[c_328]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_1595,plain,
% 7.71/1.52      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 7.71/1.52      | v1_relat_1(X0) = iProver_top
% 7.71/1.52      | v1_relat_1(k2_zfmisc_1(X1,X2)) != iProver_top ),
% 7.71/1.52      inference(predicate_to_equality,[status(thm)],[c_1594]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_1597,plain,
% 7.71/1.52      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
% 7.71/1.52      | v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
% 7.71/1.52      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 7.71/1.52      inference(instantiation,[status(thm)],[c_1595]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_875,plain,
% 7.71/1.52      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.71/1.52      theory(equality) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_1842,plain,
% 7.71/1.52      ( ~ r1_tarski(X0,X1)
% 7.71/1.52      | r1_tarski(X2,k2_zfmisc_1(X3,X4))
% 7.71/1.52      | X2 != X0
% 7.71/1.52      | k2_zfmisc_1(X3,X4) != X1 ),
% 7.71/1.52      inference(instantiation,[status(thm)],[c_875]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_1843,plain,
% 7.71/1.52      ( X0 != X1
% 7.71/1.52      | k2_zfmisc_1(X2,X3) != X4
% 7.71/1.52      | r1_tarski(X1,X4) != iProver_top
% 7.71/1.52      | r1_tarski(X0,k2_zfmisc_1(X2,X3)) = iProver_top ),
% 7.71/1.52      inference(predicate_to_equality,[status(thm)],[c_1842]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_1845,plain,
% 7.71/1.52      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 7.71/1.52      | k1_xboole_0 != k1_xboole_0
% 7.71/1.52      | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top
% 7.71/1.52      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 7.71/1.52      inference(instantiation,[status(thm)],[c_1843]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_20138,plain,
% 7.71/1.52      ( v1_relat_1(k1_relat_1(X0)) = iProver_top
% 7.71/1.52      | v1_relat_1(X0) != iProver_top
% 7.71/1.52      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 7.71/1.52      inference(global_propositional_subsumption,
% 7.71/1.52                [status(thm)],
% 7.71/1.52                [c_8492,c_89,c_106,c_107,c_116,c_1597,c_1845]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_20139,plain,
% 7.71/1.52      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 7.71/1.52      | v1_relat_1(X0) != iProver_top
% 7.71/1.52      | v1_relat_1(k1_relat_1(X0)) = iProver_top ),
% 7.71/1.52      inference(renaming,[status(thm)],[c_20138]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_20152,plain,
% 7.71/1.52      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 7.71/1.52      | v1_relat_1(k6_relat_1(X0)) != iProver_top
% 7.71/1.52      | v1_relat_1(k1_relat_1(k6_relat_1(X0))) = iProver_top ),
% 7.71/1.52      inference(superposition,[status(thm)],[c_11150,c_20139]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_20155,plain,
% 7.71/1.52      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 7.71/1.52      | v1_relat_1(X0) = iProver_top
% 7.71/1.52      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 7.71/1.52      inference(light_normalisation,[status(thm)],[c_20152,c_20]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_22203,plain,
% 7.71/1.52      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 7.71/1.52      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 7.71/1.52      | k1_relat_1(X0) = X1 ),
% 7.71/1.52      inference(global_propositional_subsumption,
% 7.71/1.52                [status(thm)],
% 7.71/1.52                [c_15277,c_17992,c_20155]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_22204,plain,
% 7.71/1.52      ( k1_relat_1(X0) = X1
% 7.71/1.52      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 7.71/1.52      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 7.71/1.52      inference(renaming,[status(thm)],[c_22203]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_22219,plain,
% 7.71/1.52      ( k1_relat_1(k6_relat_1(X0)) = X1
% 7.71/1.52      | r1_tarski(X1,X0) != iProver_top
% 7.71/1.52      | r1_tarski(k6_relat_1(X0),k1_xboole_0) != iProver_top ),
% 7.71/1.52      inference(superposition,[status(thm)],[c_20,c_22204]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_22223,plain,
% 7.71/1.52      ( X0 = X1
% 7.71/1.52      | r1_tarski(X0,X1) != iProver_top
% 7.71/1.52      | r1_tarski(k6_relat_1(X1),k1_xboole_0) != iProver_top ),
% 7.71/1.52      inference(demodulation,[status(thm)],[c_22219,c_20]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_22344,plain,
% 7.71/1.52      ( X0 = X1
% 7.71/1.52      | r1_tarski(X0,X1) != iProver_top
% 7.71/1.52      | r1_tarski(X1,k1_xboole_0) != iProver_top
% 7.71/1.52      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 7.71/1.52      inference(superposition,[status(thm)],[c_11150,c_22223]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_24490,plain,
% 7.71/1.52      ( k1_relat_1(sK4) = sK1
% 7.71/1.52      | r1_tarski(sK1,k1_xboole_0) != iProver_top
% 7.71/1.52      | v1_relat_1(k6_relat_1(sK1)) != iProver_top
% 7.71/1.52      | v1_relat_1(sK4) != iProver_top ),
% 7.71/1.52      inference(superposition,[status(thm)],[c_1799,c_22344]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_1485,plain,
% 7.71/1.52      ( ~ r1_tarski(X0,X1)
% 7.71/1.52      | r1_tarski(sK1,k1_xboole_0)
% 7.71/1.52      | sK1 != X0
% 7.71/1.52      | k1_xboole_0 != X1 ),
% 7.71/1.52      inference(instantiation,[status(thm)],[c_875]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_1486,plain,
% 7.71/1.52      ( sK1 != X0
% 7.71/1.52      | k1_xboole_0 != X1
% 7.71/1.52      | r1_tarski(X0,X1) != iProver_top
% 7.71/1.52      | r1_tarski(sK1,k1_xboole_0) = iProver_top ),
% 7.71/1.52      inference(predicate_to_equality,[status(thm)],[c_1485]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_1488,plain,
% 7.71/1.52      ( sK1 != k1_xboole_0
% 7.71/1.52      | k1_xboole_0 != k1_xboole_0
% 7.71/1.52      | r1_tarski(sK1,k1_xboole_0) = iProver_top
% 7.71/1.52      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 7.71/1.52      inference(instantiation,[status(thm)],[c_1486]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_27,plain,
% 7.71/1.52      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 7.71/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 7.71/1.52      | k1_xboole_0 = X1
% 7.71/1.52      | k1_xboole_0 = X0 ),
% 7.71/1.52      inference(cnf_transformation,[],[f95]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_36,negated_conjecture,
% 7.71/1.52      ( v1_funct_2(sK4,sK1,sK2) ),
% 7.71/1.52      inference(cnf_transformation,[],[f84]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_540,plain,
% 7.71/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 7.71/1.52      | sK2 != k1_xboole_0
% 7.71/1.52      | sK1 != X1
% 7.71/1.52      | sK4 != X0
% 7.71/1.52      | k1_xboole_0 = X0
% 7.71/1.52      | k1_xboole_0 = X1 ),
% 7.71/1.52      inference(resolution_lifted,[status(thm)],[c_27,c_36]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_541,plain,
% 7.71/1.52      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
% 7.71/1.52      | sK2 != k1_xboole_0
% 7.71/1.52      | k1_xboole_0 = sK1
% 7.71/1.52      | k1_xboole_0 = sK4 ),
% 7.71/1.52      inference(unflattening,[status(thm)],[c_540]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_1405,plain,
% 7.71/1.52      ( sK2 != k1_xboole_0
% 7.71/1.52      | k1_xboole_0 = sK1
% 7.71/1.52      | k1_xboole_0 = sK4
% 7.71/1.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
% 7.71/1.52      inference(predicate_to_equality,[status(thm)],[c_541]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_1425,plain,
% 7.71/1.52      ( sK2 != k1_xboole_0
% 7.71/1.52      | sK1 = k1_xboole_0
% 7.71/1.52      | sK4 = k1_xboole_0
% 7.71/1.52      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.71/1.52      inference(demodulation,[status(thm)],[c_1405,c_6]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_33,negated_conjecture,
% 7.71/1.52      ( k1_xboole_0 != sK2 | k1_xboole_0 = sK1 ),
% 7.71/1.52      inference(cnf_transformation,[],[f87]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_874,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_1462,plain,
% 7.71/1.52      ( sK1 != X0 | sK1 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 7.71/1.52      inference(instantiation,[status(thm)],[c_874]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_1517,plain,
% 7.71/1.52      ( sK1 != sK1 | sK1 = k1_xboole_0 | k1_xboole_0 != sK1 ),
% 7.71/1.52      inference(instantiation,[status(thm)],[c_1462]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_873,plain,( X0 = X0 ),theory(equality) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_1584,plain,
% 7.71/1.52      ( sK1 = sK1 ),
% 7.71/1.52      inference(instantiation,[status(thm)],[c_873]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_1704,plain,
% 7.71/1.52      ( sK2 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK2 ),
% 7.71/1.52      inference(instantiation,[status(thm)],[c_874]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_1705,plain,
% 7.71/1.52      ( sK2 != k1_xboole_0 | k1_xboole_0 = sK2 | k1_xboole_0 != k1_xboole_0 ),
% 7.71/1.52      inference(instantiation,[status(thm)],[c_1704]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_2056,plain,
% 7.71/1.52      ( sK2 != k1_xboole_0 | sK1 = k1_xboole_0 ),
% 7.71/1.52      inference(global_propositional_subsumption,
% 7.71/1.52                [status(thm)],
% 7.71/1.52                [c_1425,c_33,c_106,c_107,c_1517,c_1584,c_1705]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_2833,plain,
% 7.71/1.52      ( r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 7.71/1.52      inference(superposition,[status(thm)],[c_1410,c_1420]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_2937,plain,
% 7.71/1.52      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 7.71/1.52      | v1_relat_1(sK4) = iProver_top ),
% 7.71/1.52      inference(superposition,[status(thm)],[c_2833,c_1409]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_3205,plain,
% 7.71/1.52      ( v1_relat_1(sK4) = iProver_top ),
% 7.71/1.52      inference(superposition,[status(thm)],[c_1419,c_2937]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_31,plain,
% 7.71/1.52      ( ~ v1_funct_2(X0,X1,X2)
% 7.71/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.71/1.52      | k1_relset_1(X1,X2,X0) = X1
% 7.71/1.52      | k1_xboole_0 = X2 ),
% 7.71/1.52      inference(cnf_transformation,[],[f77]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_602,plain,
% 7.71/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.71/1.52      | k1_relset_1(X1,X2,X0) = X1
% 7.71/1.52      | sK2 != X2
% 7.71/1.52      | sK1 != X1
% 7.71/1.52      | sK4 != X0
% 7.71/1.52      | k1_xboole_0 = X2 ),
% 7.71/1.52      inference(resolution_lifted,[status(thm)],[c_31,c_36]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_603,plain,
% 7.71/1.52      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 7.71/1.52      | k1_relset_1(sK1,sK2,sK4) = sK1
% 7.71/1.52      | k1_xboole_0 = sK2 ),
% 7.71/1.52      inference(unflattening,[status(thm)],[c_602]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_605,plain,
% 7.71/1.52      ( k1_relset_1(sK1,sK2,sK4) = sK1 | k1_xboole_0 = sK2 ),
% 7.71/1.52      inference(global_propositional_subsumption,[status(thm)],[c_603,c_35]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_4125,plain,
% 7.71/1.52      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 7.71/1.52      inference(superposition,[status(thm)],[c_1410,c_1415]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_4324,plain,
% 7.71/1.52      ( k1_relat_1(sK4) = sK1 | sK2 = k1_xboole_0 ),
% 7.71/1.52      inference(superposition,[status(thm)],[c_605,c_4125]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_24756,plain,
% 7.71/1.52      ( v1_relat_1(k6_relat_1(sK1)) != iProver_top | k1_relat_1(sK4) = sK1 ),
% 7.71/1.52      inference(global_propositional_subsumption,
% 7.71/1.52                [status(thm)],
% 7.71/1.52                [c_24490,c_106,c_107,c_116,c_1488,c_2056,c_3205,c_4324]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_24757,plain,
% 7.71/1.52      ( k1_relat_1(sK4) = sK1 | v1_relat_1(k6_relat_1(sK1)) != iProver_top ),
% 7.71/1.52      inference(renaming,[status(thm)],[c_24756]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_24760,plain,
% 7.71/1.52      ( k1_relat_1(sK4) = sK1 ),
% 7.71/1.52      inference(superposition,[status(thm)],[c_17992,c_24757]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_35236,plain,
% 7.71/1.52      ( k1_relset_1(X0,sK3,sK4) = sK1
% 7.71/1.52      | r1_tarski(sK1,X0) != iProver_top
% 7.71/1.52      | v1_relat_1(sK4) != iProver_top ),
% 7.71/1.52      inference(light_normalisation,[status(thm)],[c_35231,c_24760]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_36666,plain,
% 7.71/1.52      ( r1_tarski(sK1,X0) != iProver_top | k1_relset_1(X0,sK3,sK4) = sK1 ),
% 7.71/1.52      inference(global_propositional_subsumption,
% 7.71/1.52                [status(thm)],
% 7.71/1.52                [c_35236,c_3205]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_36667,plain,
% 7.71/1.52      ( k1_relset_1(X0,sK3,sK4) = sK1 | r1_tarski(sK1,X0) != iProver_top ),
% 7.71/1.52      inference(renaming,[status(thm)],[c_36666]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_36672,plain,
% 7.71/1.52      ( k1_relset_1(sK1,sK3,sK4) = sK1 ),
% 7.71/1.52      inference(superposition,[status(thm)],[c_1422,c_36667]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_29,plain,
% 7.71/1.52      ( v1_funct_2(X0,X1,X2)
% 7.71/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.71/1.52      | k1_relset_1(X1,X2,X0) != X1
% 7.71/1.52      | k1_xboole_0 = X2 ),
% 7.71/1.52      inference(cnf_transformation,[],[f79]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_32,negated_conjecture,
% 7.71/1.52      ( ~ v1_funct_2(sK4,sK1,sK3)
% 7.71/1.52      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 7.71/1.52      | ~ v1_funct_1(sK4) ),
% 7.71/1.52      inference(cnf_transformation,[],[f88]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_37,negated_conjecture,
% 7.71/1.52      ( v1_funct_1(sK4) ),
% 7.71/1.52      inference(cnf_transformation,[],[f83]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_193,plain,
% 7.71/1.52      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 7.71/1.52      | ~ v1_funct_2(sK4,sK1,sK3) ),
% 7.71/1.52      inference(global_propositional_subsumption,[status(thm)],[c_32,c_37]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_194,negated_conjecture,
% 7.71/1.52      ( ~ v1_funct_2(sK4,sK1,sK3)
% 7.71/1.52      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
% 7.71/1.52      inference(renaming,[status(thm)],[c_193]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_589,plain,
% 7.71/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.71/1.52      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 7.71/1.52      | k1_relset_1(X1,X2,X0) != X1
% 7.71/1.52      | sK3 != X2
% 7.71/1.52      | sK1 != X1
% 7.71/1.52      | sK4 != X0
% 7.71/1.52      | k1_xboole_0 = X2 ),
% 7.71/1.52      inference(resolution_lifted,[status(thm)],[c_29,c_194]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_590,plain,
% 7.71/1.52      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 7.71/1.52      | k1_relset_1(sK1,sK3,sK4) != sK1
% 7.71/1.52      | k1_xboole_0 = sK3 ),
% 7.71/1.52      inference(unflattening,[status(thm)],[c_589]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_1402,plain,
% 7.71/1.52      ( k1_relset_1(sK1,sK3,sK4) != sK1
% 7.71/1.52      | k1_xboole_0 = sK3
% 7.71/1.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
% 7.71/1.52      inference(predicate_to_equality,[status(thm)],[c_590]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_36864,plain,
% 7.71/1.52      ( sK3 = k1_xboole_0
% 7.71/1.52      | sK1 != sK1
% 7.71/1.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
% 7.71/1.52      inference(demodulation,[status(thm)],[c_36672,c_1402]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_36866,plain,
% 7.71/1.52      ( sK3 = k1_xboole_0
% 7.71/1.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
% 7.71/1.52      inference(equality_resolution_simp,[status(thm)],[c_36864]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_1468,plain,
% 7.71/1.52      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 7.71/1.52      | ~ r1_tarski(k2_relat_1(sK4),sK3)
% 7.71/1.52      | ~ r1_tarski(k1_relat_1(sK4),sK1)
% 7.71/1.52      | ~ v1_relat_1(sK4) ),
% 7.71/1.52      inference(instantiation,[status(thm)],[c_24]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_1800,plain,
% 7.71/1.52      ( r1_tarski(k1_relat_1(sK4),sK1) | ~ v1_relat_1(sK4) ),
% 7.71/1.52      inference(predicate_to_equality_rev,[status(thm)],[c_1799]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_1709,plain,
% 7.71/1.52      ( sK3 != X0 | sK3 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 7.71/1.52      inference(instantiation,[status(thm)],[c_874]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_1964,plain,
% 7.71/1.52      ( sK3 != sK3 | sK3 = k1_xboole_0 | k1_xboole_0 != sK3 ),
% 7.71/1.52      inference(instantiation,[status(thm)],[c_1709]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_2700,plain,
% 7.71/1.52      ( sK3 = sK3 ),
% 7.71/1.52      inference(instantiation,[status(thm)],[c_873]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_3206,plain,
% 7.71/1.52      ( v1_relat_1(sK4) ),
% 7.71/1.52      inference(predicate_to_equality_rev,[status(thm)],[c_3205]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_3944,plain,
% 7.71/1.52      ( r1_tarski(k2_relat_1(sK4),sK3) ),
% 7.71/1.52      inference(predicate_to_equality_rev,[status(thm)],[c_3941]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_36868,plain,
% 7.71/1.52      ( sK3 = k1_xboole_0 ),
% 7.71/1.52      inference(global_propositional_subsumption,
% 7.71/1.52                [status(thm)],
% 7.71/1.52                [c_36866,c_590,c_1468,c_1800,c_1964,c_2700,c_3206,c_3944,
% 7.71/1.52                 c_36672]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_28,plain,
% 7.71/1.52      ( v1_funct_2(X0,k1_xboole_0,X1)
% 7.71/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.71/1.52      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 7.71/1.52      inference(cnf_transformation,[],[f96]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_560,plain,
% 7.71/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.71/1.52      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 7.71/1.52      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 7.71/1.52      | sK3 != X1
% 7.71/1.52      | sK1 != k1_xboole_0
% 7.71/1.52      | sK4 != X0 ),
% 7.71/1.52      inference(resolution_lifted,[status(thm)],[c_28,c_194]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_561,plain,
% 7.71/1.52      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 7.71/1.52      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)))
% 7.71/1.52      | k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
% 7.71/1.52      | sK1 != k1_xboole_0 ),
% 7.71/1.52      inference(unflattening,[status(thm)],[c_560]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_1404,plain,
% 7.71/1.52      ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
% 7.71/1.52      | sK1 != k1_xboole_0
% 7.71/1.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
% 7.71/1.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top ),
% 7.71/1.52      inference(predicate_to_equality,[status(thm)],[c_561]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_1426,plain,
% 7.71/1.52      ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
% 7.71/1.52      | sK1 != k1_xboole_0
% 7.71/1.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
% 7.71/1.52      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.71/1.52      inference(demodulation,[status(thm)],[c_1404,c_7]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_36901,plain,
% 7.71/1.52      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) != k1_xboole_0
% 7.71/1.52      | sK1 != k1_xboole_0
% 7.71/1.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top
% 7.71/1.52      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.71/1.52      inference(demodulation,[status(thm)],[c_36868,c_1426]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_36904,plain,
% 7.71/1.52      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) != k1_xboole_0
% 7.71/1.52      | sK1 != k1_xboole_0
% 7.71/1.52      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.71/1.52      inference(demodulation,[status(thm)],[c_36901,c_6]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_103,plain,
% 7.71/1.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.71/1.52      | r1_tarski(X0,X1) != iProver_top ),
% 7.71/1.52      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_105,plain,
% 7.71/1.52      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 7.71/1.52      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 7.71/1.52      inference(instantiation,[status(thm)],[c_103]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_26,plain,
% 7.71/1.52      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 7.71/1.52      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 7.71/1.52      | k1_xboole_0 = X0 ),
% 7.71/1.52      inference(cnf_transformation,[],[f94]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_517,plain,
% 7.71/1.52      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 7.71/1.52      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 7.71/1.52      | sK3 != k1_xboole_0
% 7.71/1.52      | sK1 != X0
% 7.71/1.52      | sK4 != k1_xboole_0
% 7.71/1.52      | k1_xboole_0 = X0 ),
% 7.71/1.52      inference(resolution_lifted,[status(thm)],[c_26,c_194]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_518,plain,
% 7.71/1.52      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 7.71/1.52      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
% 7.71/1.52      | sK3 != k1_xboole_0
% 7.71/1.52      | sK4 != k1_xboole_0
% 7.71/1.52      | k1_xboole_0 = sK1 ),
% 7.71/1.52      inference(unflattening,[status(thm)],[c_517]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_1406,plain,
% 7.71/1.52      ( sK3 != k1_xboole_0
% 7.71/1.52      | sK4 != k1_xboole_0
% 7.71/1.52      | k1_xboole_0 = sK1
% 7.71/1.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
% 7.71/1.52      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
% 7.71/1.52      inference(predicate_to_equality,[status(thm)],[c_518]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_1427,plain,
% 7.71/1.52      ( sK3 != k1_xboole_0
% 7.71/1.52      | sK1 = k1_xboole_0
% 7.71/1.52      | sK4 != k1_xboole_0
% 7.71/1.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
% 7.71/1.52      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.71/1.52      inference(demodulation,[status(thm)],[c_1406,c_6]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_1469,plain,
% 7.71/1.52      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) = iProver_top
% 7.71/1.52      | r1_tarski(k2_relat_1(sK4),sK3) != iProver_top
% 7.71/1.52      | r1_tarski(k1_relat_1(sK4),sK1) != iProver_top
% 7.71/1.52      | v1_relat_1(sK4) != iProver_top ),
% 7.71/1.52      inference(predicate_to_equality,[status(thm)],[c_1468]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_1587,plain,
% 7.71/1.52      ( sK4 = sK4 ),
% 7.71/1.52      inference(instantiation,[status(thm)],[c_873]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_1529,plain,
% 7.71/1.52      ( X0 != X1 | sK4 != X1 | sK4 = X0 ),
% 7.71/1.52      inference(instantiation,[status(thm)],[c_874]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_1653,plain,
% 7.71/1.52      ( X0 != sK4 | sK4 = X0 | sK4 != sK4 ),
% 7.71/1.52      inference(instantiation,[status(thm)],[c_1529]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_1654,plain,
% 7.71/1.52      ( sK4 != sK4 | sK4 = k1_xboole_0 | k1_xboole_0 != sK4 ),
% 7.71/1.52      inference(instantiation,[status(thm)],[c_1653]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_17,plain,
% 7.71/1.52      ( ~ v1_relat_1(X0) | k2_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 7.71/1.52      inference(cnf_transformation,[],[f69]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_2593,plain,
% 7.71/1.52      ( ~ v1_relat_1(sK4)
% 7.71/1.52      | k2_relat_1(sK4) != k1_xboole_0
% 7.71/1.52      | k1_xboole_0 = sK4 ),
% 7.71/1.52      inference(instantiation,[status(thm)],[c_17]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_2602,plain,
% 7.71/1.52      ( k2_relat_1(sK4) != k1_xboole_0
% 7.71/1.52      | k1_xboole_0 = sK4
% 7.71/1.52      | v1_relat_1(sK4) != iProver_top ),
% 7.71/1.52      inference(predicate_to_equality,[status(thm)],[c_2593]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_0,plain,
% 7.71/1.52      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 7.71/1.52      inference(cnf_transformation,[],[f51]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_11,plain,
% 7.71/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.71/1.52      | ~ r2_hidden(X2,X0)
% 7.71/1.52      | ~ v1_xboole_0(X1) ),
% 7.71/1.52      inference(cnf_transformation,[],[f62]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_327,plain,
% 7.71/1.52      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | ~ v1_xboole_0(X1) ),
% 7.71/1.52      inference(bin_hyper_res,[status(thm)],[c_11,c_265]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_454,plain,
% 7.71/1.52      ( ~ r1_tarski(X0,X1)
% 7.71/1.52      | ~ v1_xboole_0(X1)
% 7.71/1.52      | X0 != X2
% 7.71/1.52      | sK0(X2) != X3
% 7.71/1.52      | k1_xboole_0 = X2 ),
% 7.71/1.52      inference(resolution_lifted,[status(thm)],[c_0,c_327]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_455,plain,
% 7.71/1.52      ( ~ r1_tarski(X0,X1) | ~ v1_xboole_0(X1) | k1_xboole_0 = X0 ),
% 7.71/1.52      inference(unflattening,[status(thm)],[c_454]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_4,plain,
% 7.71/1.52      ( r1_xboole_0(X0,k1_xboole_0) ),
% 7.71/1.52      inference(cnf_transformation,[],[f55]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_5,plain,
% 7.71/1.52      ( ~ r1_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) | v1_xboole_0(X0) ),
% 7.71/1.52      inference(cnf_transformation,[],[f56]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_439,plain,
% 7.71/1.52      ( ~ r1_tarski(X0,X1) | v1_xboole_0(X0) | X0 != X2 | k1_xboole_0 != X1 ),
% 7.71/1.52      inference(resolution_lifted,[status(thm)],[c_4,c_5]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_440,plain,
% 7.71/1.52      ( ~ r1_tarski(X0,k1_xboole_0) | v1_xboole_0(X0) ),
% 7.71/1.52      inference(unflattening,[status(thm)],[c_439]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_473,plain,
% 7.71/1.52      ( ~ r1_tarski(X0,X1)
% 7.71/1.52      | ~ r1_tarski(X2,k1_xboole_0)
% 7.71/1.52      | X2 != X1
% 7.71/1.52      | k1_xboole_0 = X0 ),
% 7.71/1.52      inference(resolution_lifted,[status(thm)],[c_455,c_440]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_474,plain,
% 7.71/1.52      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,k1_xboole_0) | k1_xboole_0 = X0 ),
% 7.71/1.52      inference(unflattening,[status(thm)],[c_473]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_1408,plain,
% 7.71/1.52      ( k1_xboole_0 = X0
% 7.71/1.52      | r1_tarski(X0,X1) != iProver_top
% 7.71/1.52      | r1_tarski(X1,k1_xboole_0) != iProver_top ),
% 7.71/1.52      inference(predicate_to_equality,[status(thm)],[c_474]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_2307,plain,
% 7.71/1.52      ( k2_relset_1(sK1,sK2,sK4) = k1_xboole_0
% 7.71/1.52      | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
% 7.71/1.52      inference(superposition,[status(thm)],[c_1411,c_1408]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_3940,plain,
% 7.71/1.52      ( k2_relat_1(sK4) = k1_xboole_0
% 7.71/1.52      | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
% 7.71/1.52      inference(demodulation,[status(thm)],[c_3776,c_2307]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_3943,plain,
% 7.71/1.52      ( ~ r1_tarski(sK3,k1_xboole_0) | k2_relat_1(sK4) = k1_xboole_0 ),
% 7.71/1.52      inference(predicate_to_equality_rev,[status(thm)],[c_3940]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_1956,plain,
% 7.71/1.52      ( ~ r1_tarski(X0,X1)
% 7.71/1.52      | r1_tarski(sK3,k1_xboole_0)
% 7.71/1.52      | sK3 != X0
% 7.71/1.52      | k1_xboole_0 != X1 ),
% 7.71/1.52      inference(instantiation,[status(thm)],[c_875]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_2729,plain,
% 7.71/1.52      ( ~ r1_tarski(sK3,X0)
% 7.71/1.52      | r1_tarski(sK3,k1_xboole_0)
% 7.71/1.52      | sK3 != sK3
% 7.71/1.52      | k1_xboole_0 != X0 ),
% 7.71/1.52      inference(instantiation,[status(thm)],[c_1956]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_4771,plain,
% 7.71/1.52      ( ~ r1_tarski(sK3,sK3)
% 7.71/1.52      | r1_tarski(sK3,k1_xboole_0)
% 7.71/1.52      | sK3 != sK3
% 7.71/1.52      | k1_xboole_0 != sK3 ),
% 7.71/1.52      inference(instantiation,[status(thm)],[c_2729]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_4805,plain,
% 7.71/1.52      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 7.71/1.52      | r1_tarski(k2_relat_1(sK4),k1_xboole_0) != iProver_top
% 7.71/1.52      | v1_relat_1(sK4) != iProver_top ),
% 7.71/1.52      inference(superposition,[status(thm)],[c_1799,c_3521]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_4936,plain,
% 7.71/1.52      ( r1_tarski(k2_relat_1(sK4),k1_xboole_0) != iProver_top
% 7.71/1.52      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 7.71/1.52      inference(global_propositional_subsumption,[status(thm)],[c_4805,c_3205]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_4937,plain,
% 7.71/1.52      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 7.71/1.52      | r1_tarski(k2_relat_1(sK4),k1_xboole_0) != iProver_top ),
% 7.71/1.52      inference(renaming,[status(thm)],[c_4936]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_6983,plain,
% 7.71/1.52      ( ~ r1_tarski(X0,X1)
% 7.71/1.52      | r1_tarski(k2_relat_1(sK4),X2)
% 7.71/1.52      | X2 != X1
% 7.71/1.52      | k2_relat_1(sK4) != X0 ),
% 7.71/1.52      inference(instantiation,[status(thm)],[c_875]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_6984,plain,
% 7.71/1.52      ( X0 != X1
% 7.71/1.52      | k2_relat_1(sK4) != X2
% 7.71/1.52      | r1_tarski(X2,X1) != iProver_top
% 7.71/1.52      | r1_tarski(k2_relat_1(sK4),X0) = iProver_top ),
% 7.71/1.52      inference(predicate_to_equality,[status(thm)],[c_6983]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_6986,plain,
% 7.71/1.52      ( k2_relat_1(sK4) != k1_xboole_0
% 7.71/1.52      | k1_xboole_0 != k1_xboole_0
% 7.71/1.52      | r1_tarski(k2_relat_1(sK4),k1_xboole_0) = iProver_top
% 7.71/1.52      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 7.71/1.52      inference(instantiation,[status(thm)],[c_6984]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_9619,plain,
% 7.71/1.52      ( r1_tarski(sK3,sK3) ),
% 7.71/1.52      inference(instantiation,[status(thm)],[c_3]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_37702,plain,
% 7.71/1.52      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) != k1_xboole_0 ),
% 7.71/1.52      inference(global_propositional_subsumption,
% 7.71/1.52                [status(thm)],
% 7.71/1.52                [c_36904,c_106,c_107,c_116,c_590,c_1468,c_1469,c_1587,c_1654,
% 7.71/1.52                 c_1799,c_1800,c_1964,c_2052,c_2602,c_2700,c_3205,c_3206,
% 7.71/1.52                 c_3943,c_3941,c_3944,c_4771,c_4805,c_6986,c_9619,c_36672]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_2051,plain,
% 7.71/1.52      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
% 7.71/1.52      | sK4 != k1_xboole_0
% 7.71/1.52      | sK1 = k1_xboole_0
% 7.71/1.52      | sK3 != k1_xboole_0 ),
% 7.71/1.52      inference(global_propositional_subsumption,
% 7.71/1.52                [status(thm)],
% 7.71/1.52                [c_1427,c_105,c_116]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_2052,plain,
% 7.71/1.52      ( sK3 != k1_xboole_0
% 7.71/1.52      | sK1 = k1_xboole_0
% 7.71/1.52      | sK4 != k1_xboole_0
% 7.71/1.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
% 7.71/1.52      inference(renaming,[status(thm)],[c_2051]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_36900,plain,
% 7.71/1.52      ( sK1 = k1_xboole_0
% 7.71/1.52      | sK4 != k1_xboole_0
% 7.71/1.52      | k1_xboole_0 != k1_xboole_0
% 7.71/1.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
% 7.71/1.52      inference(demodulation,[status(thm)],[c_36868,c_2052]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_36905,plain,
% 7.71/1.52      ( sK1 = k1_xboole_0
% 7.71/1.52      | sK4 != k1_xboole_0
% 7.71/1.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
% 7.71/1.52      inference(equality_resolution_simp,[status(thm)],[c_36900]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_36906,plain,
% 7.71/1.52      ( sK1 = k1_xboole_0
% 7.71/1.52      | sK4 != k1_xboole_0
% 7.71/1.52      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.71/1.52      inference(demodulation,[status(thm)],[c_36905,c_6]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_37394,plain,
% 7.71/1.52      ( sK1 = k1_xboole_0 ),
% 7.71/1.52      inference(global_propositional_subsumption,
% 7.71/1.52                [status(thm)],
% 7.71/1.52                [c_36906,c_590,c_1468,c_1469,c_1587,c_1654,c_1799,c_1800,
% 7.71/1.52                 c_1964,c_2052,c_2602,c_2700,c_3205,c_3206,c_3943,c_3941,
% 7.71/1.52                 c_3944,c_4771,c_9619,c_36672]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_18,plain,
% 7.71/1.52      ( ~ v1_relat_1(X0) | k1_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 7.71/1.52      inference(cnf_transformation,[],[f68]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_1416,plain,
% 7.71/1.52      ( k1_relat_1(X0) != k1_xboole_0
% 7.71/1.52      | k1_xboole_0 = X0
% 7.71/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.71/1.52      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_4393,plain,
% 7.71/1.52      ( sK2 = k1_xboole_0
% 7.71/1.52      | sK1 != k1_xboole_0
% 7.71/1.52      | sK4 = k1_xboole_0
% 7.71/1.52      | v1_relat_1(sK4) != iProver_top ),
% 7.71/1.52      inference(superposition,[status(thm)],[c_4324,c_1416]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_2308,plain,
% 7.71/1.52      ( k1_relat_1(sK4) = k1_xboole_0
% 7.71/1.52      | r1_tarski(sK1,k1_xboole_0) != iProver_top
% 7.71/1.52      | v1_relat_1(sK4) != iProver_top ),
% 7.71/1.52      inference(superposition,[status(thm)],[c_1799,c_1408]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_2594,plain,
% 7.71/1.52      ( ~ v1_relat_1(sK4)
% 7.71/1.52      | k1_relat_1(sK4) != k1_xboole_0
% 7.71/1.52      | k1_xboole_0 = sK4 ),
% 7.71/1.52      inference(instantiation,[status(thm)],[c_18]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_4641,plain,
% 7.71/1.52      ( sK4 = k1_xboole_0 | sK1 != k1_xboole_0 ),
% 7.71/1.52      inference(global_propositional_subsumption,
% 7.71/1.52                [status(thm)],
% 7.71/1.52                [c_4393,c_106,c_107,c_116,c_1488,c_1587,c_1654,c_2308,c_2594,
% 7.71/1.52                 c_3205,c_3206]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_4642,plain,
% 7.71/1.52      ( sK1 != k1_xboole_0 | sK4 = k1_xboole_0 ),
% 7.71/1.52      inference(renaming,[status(thm)],[c_4641]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_37512,plain,
% 7.71/1.52      ( sK4 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 7.71/1.52      inference(demodulation,[status(thm)],[c_37394,c_4642]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_37526,plain,
% 7.71/1.52      ( sK4 = k1_xboole_0 ),
% 7.71/1.52      inference(equality_resolution_simp,[status(thm)],[c_37512]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_37704,plain,
% 7.71/1.52      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
% 7.71/1.52      inference(light_normalisation,[status(thm)],[c_37702,c_37526]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_16,plain,
% 7.71/1.52      ( r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
% 7.71/1.52      inference(cnf_transformation,[],[f67]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_1418,plain,
% 7.71/1.52      ( r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) = iProver_top ),
% 7.71/1.52      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_2202,plain,
% 7.71/1.52      ( r1_tarski(k2_relat_1(k1_xboole_0),X0) = iProver_top ),
% 7.71/1.52      inference(superposition,[status(thm)],[c_7,c_1418]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_2305,plain,
% 7.71/1.52      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 7.71/1.52      inference(superposition,[status(thm)],[c_1422,c_1408]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_2689,plain,
% 7.71/1.52      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.71/1.52      inference(superposition,[status(thm)],[c_2202,c_2305]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_2783,plain,
% 7.71/1.52      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.71/1.52      inference(demodulation,[status(thm)],[c_2689,c_2202]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_4122,plain,
% 7.71/1.52      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.71/1.52      | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 7.71/1.52      inference(superposition,[status(thm)],[c_1421,c_1415]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_13488,plain,
% 7.71/1.52      ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 7.71/1.52      inference(superposition,[status(thm)],[c_2783,c_4122]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_2534,plain,
% 7.71/1.52      ( m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 7.71/1.52      inference(superposition,[status(thm)],[c_6,c_1412]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_2834,plain,
% 7.71/1.52      ( r1_tarski(k6_relat_1(k1_xboole_0),k1_xboole_0) = iProver_top ),
% 7.71/1.52      inference(superposition,[status(thm)],[c_2534,c_1420]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_3463,plain,
% 7.71/1.52      ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.71/1.52      inference(superposition,[status(thm)],[c_2834,c_2305]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_3469,plain,
% 7.71/1.52      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.71/1.52      inference(superposition,[status(thm)],[c_3463,c_20]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_13495,plain,
% 7.71/1.52      ( k1_relset_1(X0,X1,k1_xboole_0) = k1_xboole_0 ),
% 7.71/1.52      inference(light_normalisation,[status(thm)],[c_13488,c_3469]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_37705,plain,
% 7.71/1.52      ( k1_xboole_0 != k1_xboole_0 ),
% 7.71/1.52      inference(demodulation,[status(thm)],[c_37704,c_13495]) ).
% 7.71/1.52  
% 7.71/1.52  cnf(c_37706,plain,
% 7.71/1.52      ( $false ),
% 7.71/1.52      inference(equality_resolution_simp,[status(thm)],[c_37705]) ).
% 7.71/1.52  
% 7.71/1.52  
% 7.71/1.52  % SZS output end CNFRefutation for theBenchmark.p
% 7.71/1.52  
% 7.71/1.52  ------                               Statistics
% 7.71/1.52  
% 7.71/1.52  ------ General
% 7.71/1.52  
% 7.71/1.52  abstr_ref_over_cycles:                  0
% 7.71/1.52  abstr_ref_under_cycles:                 0
% 7.71/1.52  gc_basic_clause_elim:                   0
% 7.71/1.52  forced_gc_time:                         0
% 7.71/1.52  parsing_time:                           0.008
% 7.71/1.52  unif_index_cands_time:                  0.
% 7.71/1.52  unif_index_add_time:                    0.
% 7.71/1.52  orderings_time:                         0.
% 7.71/1.52  out_proof_time:                         0.02
% 7.71/1.52  total_time:                             0.966
% 7.71/1.52  num_of_symbols:                         53
% 7.71/1.52  num_of_terms:                           24727
% 7.71/1.52  
% 7.71/1.52  ------ Preprocessing
% 7.71/1.52  
% 7.71/1.52  num_of_splits:                          0
% 7.71/1.52  num_of_split_atoms:                     0
% 7.71/1.52  num_of_reused_defs:                     0
% 7.71/1.52  num_eq_ax_congr_red:                    11
% 7.71/1.52  num_of_sem_filtered_clauses:            2
% 7.71/1.52  num_of_subtypes:                        0
% 7.71/1.52  monotx_restored_types:                  0
% 7.71/1.52  sat_num_of_epr_types:                   0
% 7.71/1.52  sat_num_of_non_cyclic_types:            0
% 7.71/1.52  sat_guarded_non_collapsed_types:        0
% 7.71/1.52  num_pure_diseq_elim:                    0
% 7.71/1.52  simp_replaced_by:                       0
% 7.71/1.52  res_preprocessed:                       150
% 7.71/1.52  prep_upred:                             0
% 7.71/1.52  prep_unflattend:                        38
% 7.71/1.52  smt_new_axioms:                         0
% 7.71/1.52  pred_elim_cands:                        3
% 7.71/1.52  pred_elim:                              5
% 7.71/1.52  pred_elim_cl:                           6
% 7.71/1.52  pred_elim_cycles:                       7
% 7.71/1.52  merged_defs:                            8
% 7.71/1.52  merged_defs_ncl:                        0
% 7.71/1.52  bin_hyper_res:                          10
% 7.71/1.52  prep_cycles:                            4
% 7.71/1.52  pred_elim_time:                         0.005
% 7.71/1.52  splitting_time:                         0.
% 7.71/1.52  sem_filter_time:                        0.
% 7.71/1.52  monotx_time:                            0.001
% 7.71/1.52  subtype_inf_time:                       0.
% 7.71/1.52  
% 7.71/1.52  ------ Problem properties
% 7.71/1.52  
% 7.71/1.52  clauses:                                30
% 7.71/1.52  conjectures:                            3
% 7.71/1.52  epr:                                    5
% 7.71/1.52  horn:                                   27
% 7.71/1.52  ground:                                 10
% 7.71/1.52  unary:                                  10
% 7.71/1.52  binary:                                 7
% 7.71/1.52  lits:                                   68
% 7.71/1.52  lits_eq:                                32
% 7.71/1.52  fd_pure:                                0
% 7.71/1.52  fd_pseudo:                              0
% 7.71/1.52  fd_cond:                                4
% 7.71/1.52  fd_pseudo_cond:                         1
% 7.71/1.52  ac_symbols:                             0
% 7.71/1.52  
% 7.71/1.52  ------ Propositional Solver
% 7.71/1.52  
% 7.71/1.52  prop_solver_calls:                      32
% 7.71/1.52  prop_fast_solver_calls:                 2568
% 7.71/1.52  smt_solver_calls:                       0
% 7.71/1.52  smt_fast_solver_calls:                  0
% 7.71/1.52  prop_num_of_clauses:                    15244
% 7.71/1.52  prop_preprocess_simplified:             29462
% 7.71/1.52  prop_fo_subsumed:                       118
% 7.71/1.52  prop_solver_time:                       0.
% 7.71/1.52  smt_solver_time:                        0.
% 7.71/1.52  smt_fast_solver_time:                   0.
% 7.71/1.52  prop_fast_solver_time:                  0.
% 7.71/1.52  prop_unsat_core_time:                   0.
% 7.71/1.52  
% 7.71/1.52  ------ QBF
% 7.71/1.52  
% 7.71/1.52  qbf_q_res:                              0
% 7.71/1.52  qbf_num_tautologies:                    0
% 7.71/1.52  qbf_prep_cycles:                        0
% 7.71/1.52  
% 7.71/1.52  ------ BMC1
% 7.71/1.52  
% 7.71/1.52  bmc1_current_bound:                     -1
% 7.71/1.52  bmc1_last_solved_bound:                 -1
% 7.71/1.52  bmc1_unsat_core_size:                   -1
% 7.71/1.52  bmc1_unsat_core_parents_size:           -1
% 7.71/1.52  bmc1_merge_next_fun:                    0
% 7.71/1.52  bmc1_unsat_core_clauses_time:           0.
% 7.71/1.52  
% 7.71/1.52  ------ Instantiation
% 7.71/1.52  
% 7.71/1.52  inst_num_of_clauses:                    4507
% 7.71/1.52  inst_num_in_passive:                    1292
% 7.71/1.52  inst_num_in_active:                     2187
% 7.71/1.52  inst_num_in_unprocessed:                1028
% 7.71/1.52  inst_num_of_loops:                      2560
% 7.71/1.52  inst_num_of_learning_restarts:          0
% 7.71/1.52  inst_num_moves_active_passive:          370
% 7.71/1.52  inst_lit_activity:                      0
% 7.71/1.52  inst_lit_activity_moves:                0
% 7.71/1.52  inst_num_tautologies:                   0
% 7.71/1.52  inst_num_prop_implied:                  0
% 7.71/1.52  inst_num_existing_simplified:           0
% 7.71/1.52  inst_num_eq_res_simplified:             0
% 7.71/1.52  inst_num_child_elim:                    0
% 7.71/1.52  inst_num_of_dismatching_blockings:      2881
% 7.71/1.52  inst_num_of_non_proper_insts:           7312
% 7.71/1.52  inst_num_of_duplicates:                 0
% 7.71/1.52  inst_inst_num_from_inst_to_res:         0
% 7.71/1.52  inst_dismatching_checking_time:         0.
% 7.71/1.52  
% 7.71/1.52  ------ Resolution
% 7.71/1.52  
% 7.71/1.52  res_num_of_clauses:                     0
% 7.71/1.52  res_num_in_passive:                     0
% 7.71/1.52  res_num_in_active:                      0
% 7.71/1.52  res_num_of_loops:                       154
% 7.71/1.52  res_forward_subset_subsumed:            392
% 7.71/1.52  res_backward_subset_subsumed:           2
% 7.71/1.52  res_forward_subsumed:                   0
% 7.71/1.52  res_backward_subsumed:                  0
% 7.71/1.52  res_forward_subsumption_resolution:     0
% 7.71/1.52  res_backward_subsumption_resolution:    0
% 7.71/1.52  res_clause_to_clause_subsumption:       5879
% 7.71/1.52  res_orphan_elimination:                 0
% 7.71/1.52  res_tautology_del:                      299
% 7.71/1.52  res_num_eq_res_simplified:              1
% 7.71/1.52  res_num_sel_changes:                    0
% 7.71/1.52  res_moves_from_active_to_pass:          0
% 7.71/1.52  
% 7.71/1.52  ------ Superposition
% 7.71/1.52  
% 7.71/1.52  sup_time_total:                         0.
% 7.71/1.52  sup_time_generating:                    0.
% 7.71/1.52  sup_time_sim_full:                      0.
% 7.71/1.52  sup_time_sim_immed:                     0.
% 7.71/1.52  
% 7.71/1.52  sup_num_of_clauses:                     489
% 7.71/1.52  sup_num_in_active:                      108
% 7.71/1.52  sup_num_in_passive:                     381
% 7.71/1.52  sup_num_of_loops:                       511
% 7.71/1.52  sup_fw_superposition:                   1141
% 7.71/1.52  sup_bw_superposition:                   565
% 7.71/1.52  sup_immediate_simplified:               789
% 7.71/1.52  sup_given_eliminated:                   6
% 7.71/1.52  comparisons_done:                       0
% 7.71/1.52  comparisons_avoided:                    273
% 7.71/1.52  
% 7.71/1.52  ------ Simplifications
% 7.71/1.52  
% 7.71/1.52  
% 7.71/1.52  sim_fw_subset_subsumed:                 113
% 7.71/1.52  sim_bw_subset_subsumed:                 168
% 7.71/1.52  sim_fw_subsumed:                        186
% 7.71/1.52  sim_bw_subsumed:                        107
% 7.71/1.52  sim_fw_subsumption_res:                 0
% 7.71/1.52  sim_bw_subsumption_res:                 0
% 7.71/1.52  sim_tautology_del:                      36
% 7.71/1.52  sim_eq_tautology_del:                   174
% 7.71/1.52  sim_eq_res_simp:                        4
% 7.71/1.52  sim_fw_demodulated:                     284
% 7.71/1.52  sim_bw_demodulated:                     249
% 7.71/1.52  sim_light_normalised:                   308
% 7.71/1.52  sim_joinable_taut:                      0
% 7.71/1.52  sim_joinable_simp:                      0
% 7.71/1.52  sim_ac_normalised:                      0
% 7.71/1.52  sim_smt_subsumption:                    0
% 7.71/1.52  
%------------------------------------------------------------------------------
