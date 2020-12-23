%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:08 EST 2020

% Result     : Theorem 3.73s
% Output     : CNFRefutation 3.73s
% Verified   : 
% Statistics : Number of formulae       :  186 (3075 expanded)
%              Number of clauses        :   96 ( 591 expanded)
%              Number of leaves         :   24 ( 791 expanded)
%              Depth                    :   22
%              Number of atoms          :  500 (8592 expanded)
%              Number of equality atoms :  306 (4297 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f41])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f115,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f39,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f40,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f49,plain,
    ( ? [X0,X1,X2] :
        ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( k1_tarski(k1_funct_1(sK3,sK1)) != k2_relset_1(k1_tarski(sK1),sK2,sK3)
      & k1_xboole_0 != sK2
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
      & v1_funct_2(sK3,k1_tarski(sK1),sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( k1_tarski(k1_funct_1(sK3,sK1)) != k2_relset_1(k1_tarski(sK1),sK2,sK3)
    & k1_xboole_0 != sK2
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
    & v1_funct_2(sK3,k1_tarski(sK1),sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f40,f49])).

fof(f89,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) ),
    inference(cnf_transformation,[],[f50])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f92,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f56,f57])).

fof(f93,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f55,f92])).

fof(f113,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
    inference(definition_unfolding,[],[f89,f93])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | o_0_0_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(definition_unfolding,[],[f85,f51])).

fof(f88,plain,(
    v1_funct_2(sK3,k1_tarski(sK1),sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f114,plain,(
    v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
    inference(definition_unfolding,[],[f88,f93])).

fof(f87,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f90,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f50])).

fof(f112,plain,(
    o_0_0_xboole_0 != sK2 ),
    inference(definition_unfolding,[],[f90,f51])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
    <=> ~ ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
    <=> ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3 ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
        | ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) )
      & ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3
        | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
        | ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) )
      & ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3
        | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ) ),
    inference(flattening,[],[f43])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | k2_tarski(X0,X2) = X3
      | k2_tarski(X1,X2) = X3
      | k2_tarski(X0,X1) = X3
      | k1_tarski(X2) = X3
      | k1_tarski(X1) = X3
      | k1_tarski(X0) = X3
      | k1_xboole_0 = X3
      | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_enumset1(X0,X0,X1,X2) = X3
      | k2_enumset1(X0,X0,X0,X2) = X3
      | k2_enumset1(X1,X1,X1,X2) = X3
      | k2_enumset1(X0,X0,X0,X1) = X3
      | k2_enumset1(X2,X2,X2,X2) = X3
      | k2_enumset1(X1,X1,X1,X1) = X3
      | k2_enumset1(X0,X0,X0,X0) = X3
      | o_0_0_xboole_0 = X3
      | ~ r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) ) ),
    inference(definition_unfolding,[],[f58,f57,f92,f92,f92,f93,f93,f93,f51,f57])).

fof(f54,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f91,plain,(
    k1_tarski(k1_funct_1(sK3,sK1)) != k2_relset_1(k1_tarski(sK1),sK2,sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f111,plain,(
    k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) ),
    inference(definition_unfolding,[],[f91,f93,f93])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f108,plain,(
    ! [X0,X1] :
      ( k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f76,f93,f93])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f74,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f107,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = X0
      | o_0_0_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f74,f51,f51])).

fof(f19,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_tarski(X2) = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
    ? [X1] :
      ( k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( k1_relat_1(sK0(X0)) = X0
        & v1_funct_1(sK0(X0))
        & v1_relat_1(sK0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( k1_relat_1(sK0(X0)) = X0
      & v1_funct_1(sK0(X0))
      & v1_relat_1(sK0(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f47])).

fof(f84,plain,(
    ! [X0] : k1_relat_1(sK0(X0)) = X0 ),
    inference(cnf_transformation,[],[f48])).

fof(f82,plain,(
    ! [X0] : v1_relat_1(sK0(X0)) ),
    inference(cnf_transformation,[],[f48])).

fof(f83,plain,(
    ! [X0] : v1_funct_1(sK0(X0)) ),
    inference(cnf_transformation,[],[f48])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f104,plain,(
    o_0_0_xboole_0 = k2_relat_1(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f73,f51,f51])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f103,plain,(
    ! [X0] : m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f67,f51])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f72,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f105,plain,(
    o_0_0_xboole_0 = k1_relat_1(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f72,f51,f51])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_1574,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_1552,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1555,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3811,plain,
    ( k8_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3,X0) = k10_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1552,c_1555])).

cnf(c_31,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k8_relset_1(X1,X2,X0,X2) = X1
    | o_0_0_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f110])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_457,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k8_relset_1(X1,X2,X0,X2) = X1
    | k2_enumset1(sK1,sK1,sK1,sK1) != X1
    | sK2 != X2
    | sK3 != X0
    | o_0_0_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_35])).

cnf(c_458,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))
    | ~ v1_funct_1(sK3)
    | k8_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3,sK2) = k2_enumset1(sK1,sK1,sK1,sK1)
    | o_0_0_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_457])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_33,negated_conjecture,
    ( o_0_0_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f112])).

cnf(c_460,plain,
    ( k8_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3,sK2) = k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_458,c_36,c_34,c_33])).

cnf(c_4051,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k10_relat_1(sK3,sK2) ),
    inference(demodulation,[status(thm)],[c_3811,c_460])).

cnf(c_23,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_16,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_419,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_23,c_16])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_423,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_419,c_22])).

cnf(c_424,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_423])).

cnf(c_1550,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_424])).

cnf(c_2047,plain,
    ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK1,sK1,sK1,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1552,c_1550])).

cnf(c_4066,plain,
    ( r1_tarski(k1_relat_1(sK3),k10_relat_1(sK3,sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4051,c_2047])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X2,X3))
    | k2_enumset1(X1,X1,X2,X3) = X0
    | k2_enumset1(X1,X1,X1,X3) = X0
    | k2_enumset1(X2,X2,X2,X3) = X0
    | k2_enumset1(X1,X1,X1,X2) = X0
    | k2_enumset1(X3,X3,X3,X3) = X0
    | k2_enumset1(X2,X2,X2,X2) = X0
    | k2_enumset1(X1,X1,X1,X1) = X0
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1565,plain,
    ( k2_enumset1(X0,X0,X1,X2) = X3
    | k2_enumset1(X0,X0,X0,X2) = X3
    | k2_enumset1(X1,X1,X1,X2) = X3
    | k2_enumset1(X0,X0,X0,X1) = X3
    | k2_enumset1(X2,X2,X2,X2) = X3
    | k2_enumset1(X1,X1,X1,X1) = X3
    | k2_enumset1(X0,X0,X0,X0) = X3
    | o_0_0_xboole_0 = X3
    | r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4729,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = X0
    | o_0_0_xboole_0 = X0
    | r1_tarski(X0,k10_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4051,c_1565])).

cnf(c_4730,plain,
    ( k10_relat_1(sK3,sK2) = X0
    | o_0_0_xboole_0 = X0
    | r1_tarski(X0,k10_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4729,c_4051])).

cnf(c_5641,plain,
    ( k10_relat_1(sK3,sK2) = k1_relat_1(sK3)
    | k1_relat_1(sK3) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_4066,c_4730])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1575,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3784,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3)
    | r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2047,c_1575])).

cnf(c_32,negated_conjecture,
    ( k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_947,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1608,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != X0
    | k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) = k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3)
    | k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) != X0 ),
    inference(instantiation,[status(thm)],[c_947])).

cnf(c_1674,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) = k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3)
    | k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relat_1(sK3)
    | k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1608])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1746,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))
    | k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) = k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_21,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1934,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) = k2_relat_1(sK3)
    | k2_enumset1(sK1,sK1,sK1,sK1) != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_2072,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_2305,plain,
    ( ~ r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k1_relat_1(sK3))
    | ~ r1_tarski(k1_relat_1(sK3),k2_enumset1(sK1,sK1,sK1,sK1))
    | k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2306,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3)
    | r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k1_relat_1(sK3)) != iProver_top
    | r1_tarski(k1_relat_1(sK3),k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2305])).

cnf(c_5080,plain,
    ( r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k1_relat_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3784,c_36,c_34,c_32,c_1674,c_1746,c_1934,c_2047,c_2072,c_2306])).

cnf(c_5084,plain,
    ( r1_tarski(k10_relat_1(sK3,sK2),k1_relat_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5080,c_4051])).

cnf(c_6345,plain,
    ( k1_relat_1(sK3) = o_0_0_xboole_0
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5641,c_5084])).

cnf(c_6466,plain,
    ( k1_relat_1(sK3) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_1574,c_6345])).

cnf(c_20,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != o_0_0_xboole_0
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1560,plain,
    ( k1_relat_1(X0) != o_0_0_xboole_0
    | o_0_0_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_6759,plain,
    ( sK3 = o_0_0_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6466,c_1560])).

cnf(c_946,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1838,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_946])).

cnf(c_1714,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_947])).

cnf(c_1892,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1714])).

cnf(c_1893,plain,
    ( sK3 != sK3
    | sK3 = o_0_0_xboole_0
    | o_0_0_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_1892])).

cnf(c_2842,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) != o_0_0_xboole_0
    | o_0_0_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_6925,plain,
    ( sK3 = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6759,c_34,c_1838,c_1893,c_2072,c_2842,c_6466])).

cnf(c_27,plain,
    ( k1_relat_1(sK0(X0)) = X0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1559,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1)
    | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3911,plain,
    ( k2_enumset1(X0,X0,X0,X0) != X1
    | k2_enumset1(k1_funct_1(sK0(X1),X0),k1_funct_1(sK0(X1),X0),k1_funct_1(sK0(X1),X0),k1_funct_1(sK0(X1),X0)) = k2_relat_1(sK0(X1))
    | v1_funct_1(sK0(X1)) != iProver_top
    | v1_relat_1(sK0(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_27,c_1559])).

cnf(c_4082,plain,
    ( k2_enumset1(k1_funct_1(sK0(X0),sK1),k1_funct_1(sK0(X0),sK1),k1_funct_1(sK0(X0),sK1),k1_funct_1(sK0(X0),sK1)) = k2_relat_1(sK0(X0))
    | k10_relat_1(sK3,sK2) != X0
    | v1_funct_1(sK0(X0)) != iProver_top
    | v1_relat_1(sK0(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4051,c_3911])).

cnf(c_29,plain,
    ( v1_relat_1(sK0(X0)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_28,plain,
    ( v1_funct_1(sK0(X0)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_4090,plain,
    ( ~ v1_funct_1(sK0(X0))
    | ~ v1_relat_1(sK0(X0))
    | k2_enumset1(k1_funct_1(sK0(X0),sK1),k1_funct_1(sK0(X0),sK1),k1_funct_1(sK0(X0),sK1),k1_funct_1(sK0(X0),sK1)) = k2_relat_1(sK0(X0))
    | k10_relat_1(sK3,sK2) != X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4082])).

cnf(c_5629,plain,
    ( k2_enumset1(k1_funct_1(sK0(X0),sK1),k1_funct_1(sK0(X0),sK1),k1_funct_1(sK0(X0),sK1),k1_funct_1(sK0(X0),sK1)) = k2_relat_1(sK0(X0))
    | k10_relat_1(sK3,sK2) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4082,c_29,c_28,c_4090])).

cnf(c_5632,plain,
    ( k2_enumset1(k1_funct_1(sK0(k10_relat_1(sK3,sK2)),sK1),k1_funct_1(sK0(k10_relat_1(sK3,sK2)),sK1),k1_funct_1(sK0(k10_relat_1(sK3,sK2)),sK1),k1_funct_1(sK0(k10_relat_1(sK3,sK2)),sK1)) = k2_relat_1(sK0(k10_relat_1(sK3,sK2))) ),
    inference(equality_resolution,[status(thm)],[c_5629])).

cnf(c_6930,plain,
    ( k2_enumset1(k1_funct_1(sK0(k10_relat_1(o_0_0_xboole_0,sK2)),sK1),k1_funct_1(sK0(k10_relat_1(o_0_0_xboole_0,sK2)),sK1),k1_funct_1(sK0(k10_relat_1(o_0_0_xboole_0,sK2)),sK1),k1_funct_1(sK0(k10_relat_1(o_0_0_xboole_0,sK2)),sK1)) = k2_relat_1(sK0(k10_relat_1(o_0_0_xboole_0,sK2))) ),
    inference(demodulation,[status(thm)],[c_6925,c_5632])).

cnf(c_17,plain,
    ( k2_relat_1(o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_3091,plain,
    ( sK0(X0) = o_0_0_xboole_0
    | o_0_0_xboole_0 != X0
    | v1_relat_1(sK0(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_27,c_1560])).

cnf(c_46,plain,
    ( v1_relat_1(sK0(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3176,plain,
    ( o_0_0_xboole_0 != X0
    | sK0(X0) = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3091,c_46])).

cnf(c_3177,plain,
    ( sK0(X0) = o_0_0_xboole_0
    | o_0_0_xboole_0 != X0 ),
    inference(renaming,[status(thm)],[c_3176])).

cnf(c_3179,plain,
    ( sK0(o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_3177])).

cnf(c_12,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1564,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3808,plain,
    ( k8_relset_1(X0,X1,o_0_0_xboole_0,X2) = k10_relat_1(o_0_0_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_1564,c_1555])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1557,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4828,plain,
    ( m1_subset_1(k10_relat_1(o_0_0_xboole_0,X0),k1_zfmisc_1(X1)) = iProver_top
    | m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3808,c_1557])).

cnf(c_6270,plain,
    ( m1_subset_1(k10_relat_1(o_0_0_xboole_0,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1564,c_4828])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1562,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_6762,plain,
    ( r1_tarski(k10_relat_1(o_0_0_xboole_0,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_6270,c_1562])).

cnf(c_2295,plain,
    ( r1_tarski(k1_relat_1(o_0_0_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1564,c_1550])).

cnf(c_18,plain,
    ( k1_relat_1(o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_2296,plain,
    ( r1_tarski(o_0_0_xboole_0,X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2295,c_18])).

cnf(c_3781,plain,
    ( o_0_0_xboole_0 = X0
    | r1_tarski(X0,o_0_0_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2296,c_1575])).

cnf(c_6917,plain,
    ( k10_relat_1(o_0_0_xboole_0,X0) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_6762,c_3781])).

cnf(c_6978,plain,
    ( k2_enumset1(k1_funct_1(o_0_0_xboole_0,sK1),k1_funct_1(o_0_0_xboole_0,sK1),k1_funct_1(o_0_0_xboole_0,sK1),k1_funct_1(o_0_0_xboole_0,sK1)) = o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6930,c_17,c_3179,c_6917])).

cnf(c_1556,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3184,plain,
    ( k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1552,c_1556])).

cnf(c_3261,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_3184,c_32])).

cnf(c_6950,plain,
    ( k2_enumset1(k1_funct_1(o_0_0_xboole_0,sK1),k1_funct_1(o_0_0_xboole_0,sK1),k1_funct_1(o_0_0_xboole_0,sK1),k1_funct_1(o_0_0_xboole_0,sK1)) != k2_relat_1(o_0_0_xboole_0) ),
    inference(demodulation,[status(thm)],[c_6925,c_3261])).

cnf(c_6953,plain,
    ( k2_enumset1(k1_funct_1(o_0_0_xboole_0,sK1),k1_funct_1(o_0_0_xboole_0,sK1),k1_funct_1(o_0_0_xboole_0,sK1),k1_funct_1(o_0_0_xboole_0,sK1)) != o_0_0_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6950,c_17])).

cnf(c_6979,plain,
    ( o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6978,c_6953])).

cnf(c_6980,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_6979])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:56:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.73/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.73/1.00  
% 3.73/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.73/1.00  
% 3.73/1.00  ------  iProver source info
% 3.73/1.00  
% 3.73/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.73/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.73/1.00  git: non_committed_changes: false
% 3.73/1.00  git: last_make_outside_of_git: false
% 3.73/1.00  
% 3.73/1.00  ------ 
% 3.73/1.00  
% 3.73/1.00  ------ Input Options
% 3.73/1.00  
% 3.73/1.00  --out_options                           all
% 3.73/1.00  --tptp_safe_out                         true
% 3.73/1.00  --problem_path                          ""
% 3.73/1.00  --include_path                          ""
% 3.73/1.00  --clausifier                            res/vclausify_rel
% 3.73/1.00  --clausifier_options                    ""
% 3.73/1.00  --stdin                                 false
% 3.73/1.00  --stats_out                             all
% 3.73/1.00  
% 3.73/1.00  ------ General Options
% 3.73/1.00  
% 3.73/1.00  --fof                                   false
% 3.73/1.00  --time_out_real                         305.
% 3.73/1.00  --time_out_virtual                      -1.
% 3.73/1.00  --symbol_type_check                     false
% 3.73/1.00  --clausify_out                          false
% 3.73/1.00  --sig_cnt_out                           false
% 3.73/1.00  --trig_cnt_out                          false
% 3.73/1.00  --trig_cnt_out_tolerance                1.
% 3.73/1.00  --trig_cnt_out_sk_spl                   false
% 3.73/1.00  --abstr_cl_out                          false
% 3.73/1.00  
% 3.73/1.00  ------ Global Options
% 3.73/1.00  
% 3.73/1.00  --schedule                              default
% 3.73/1.00  --add_important_lit                     false
% 3.73/1.00  --prop_solver_per_cl                    1000
% 3.73/1.00  --min_unsat_core                        false
% 3.73/1.00  --soft_assumptions                      false
% 3.73/1.00  --soft_lemma_size                       3
% 3.73/1.00  --prop_impl_unit_size                   0
% 3.73/1.00  --prop_impl_unit                        []
% 3.73/1.00  --share_sel_clauses                     true
% 3.73/1.00  --reset_solvers                         false
% 3.73/1.00  --bc_imp_inh                            [conj_cone]
% 3.73/1.00  --conj_cone_tolerance                   3.
% 3.73/1.00  --extra_neg_conj                        none
% 3.73/1.00  --large_theory_mode                     true
% 3.73/1.00  --prolific_symb_bound                   200
% 3.73/1.00  --lt_threshold                          2000
% 3.73/1.00  --clause_weak_htbl                      true
% 3.73/1.00  --gc_record_bc_elim                     false
% 3.73/1.00  
% 3.73/1.00  ------ Preprocessing Options
% 3.73/1.00  
% 3.73/1.00  --preprocessing_flag                    true
% 3.73/1.00  --time_out_prep_mult                    0.1
% 3.73/1.00  --splitting_mode                        input
% 3.73/1.00  --splitting_grd                         true
% 3.73/1.00  --splitting_cvd                         false
% 3.73/1.00  --splitting_cvd_svl                     false
% 3.73/1.00  --splitting_nvd                         32
% 3.73/1.00  --sub_typing                            true
% 3.73/1.00  --prep_gs_sim                           true
% 3.73/1.00  --prep_unflatten                        true
% 3.73/1.00  --prep_res_sim                          true
% 3.73/1.00  --prep_upred                            true
% 3.73/1.00  --prep_sem_filter                       exhaustive
% 3.73/1.00  --prep_sem_filter_out                   false
% 3.73/1.00  --pred_elim                             true
% 3.73/1.00  --res_sim_input                         true
% 3.73/1.00  --eq_ax_congr_red                       true
% 3.73/1.00  --pure_diseq_elim                       true
% 3.73/1.00  --brand_transform                       false
% 3.73/1.00  --non_eq_to_eq                          false
% 3.73/1.00  --prep_def_merge                        true
% 3.73/1.00  --prep_def_merge_prop_impl              false
% 3.73/1.00  --prep_def_merge_mbd                    true
% 3.73/1.00  --prep_def_merge_tr_red                 false
% 3.73/1.00  --prep_def_merge_tr_cl                  false
% 3.73/1.00  --smt_preprocessing                     true
% 3.73/1.00  --smt_ac_axioms                         fast
% 3.73/1.00  --preprocessed_out                      false
% 3.73/1.00  --preprocessed_stats                    false
% 3.73/1.00  
% 3.73/1.00  ------ Abstraction refinement Options
% 3.73/1.00  
% 3.73/1.00  --abstr_ref                             []
% 3.73/1.00  --abstr_ref_prep                        false
% 3.73/1.00  --abstr_ref_until_sat                   false
% 3.73/1.00  --abstr_ref_sig_restrict                funpre
% 3.73/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.73/1.00  --abstr_ref_under                       []
% 3.73/1.00  
% 3.73/1.00  ------ SAT Options
% 3.73/1.00  
% 3.73/1.00  --sat_mode                              false
% 3.73/1.00  --sat_fm_restart_options                ""
% 3.73/1.00  --sat_gr_def                            false
% 3.73/1.00  --sat_epr_types                         true
% 3.73/1.00  --sat_non_cyclic_types                  false
% 3.73/1.00  --sat_finite_models                     false
% 3.73/1.00  --sat_fm_lemmas                         false
% 3.73/1.00  --sat_fm_prep                           false
% 3.73/1.00  --sat_fm_uc_incr                        true
% 3.73/1.00  --sat_out_model                         small
% 3.73/1.00  --sat_out_clauses                       false
% 3.73/1.00  
% 3.73/1.00  ------ QBF Options
% 3.73/1.00  
% 3.73/1.00  --qbf_mode                              false
% 3.73/1.00  --qbf_elim_univ                         false
% 3.73/1.00  --qbf_dom_inst                          none
% 3.73/1.00  --qbf_dom_pre_inst                      false
% 3.73/1.00  --qbf_sk_in                             false
% 3.73/1.00  --qbf_pred_elim                         true
% 3.73/1.00  --qbf_split                             512
% 3.73/1.00  
% 3.73/1.00  ------ BMC1 Options
% 3.73/1.00  
% 3.73/1.00  --bmc1_incremental                      false
% 3.73/1.00  --bmc1_axioms                           reachable_all
% 3.73/1.00  --bmc1_min_bound                        0
% 3.73/1.00  --bmc1_max_bound                        -1
% 3.73/1.00  --bmc1_max_bound_default                -1
% 3.73/1.00  --bmc1_symbol_reachability              true
% 3.73/1.00  --bmc1_property_lemmas                  false
% 3.73/1.00  --bmc1_k_induction                      false
% 3.73/1.00  --bmc1_non_equiv_states                 false
% 3.73/1.00  --bmc1_deadlock                         false
% 3.73/1.00  --bmc1_ucm                              false
% 3.73/1.00  --bmc1_add_unsat_core                   none
% 3.73/1.00  --bmc1_unsat_core_children              false
% 3.73/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.73/1.00  --bmc1_out_stat                         full
% 3.73/1.00  --bmc1_ground_init                      false
% 3.73/1.00  --bmc1_pre_inst_next_state              false
% 3.73/1.00  --bmc1_pre_inst_state                   false
% 3.73/1.00  --bmc1_pre_inst_reach_state             false
% 3.73/1.00  --bmc1_out_unsat_core                   false
% 3.73/1.00  --bmc1_aig_witness_out                  false
% 3.73/1.00  --bmc1_verbose                          false
% 3.73/1.00  --bmc1_dump_clauses_tptp                false
% 3.73/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.73/1.00  --bmc1_dump_file                        -
% 3.73/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.73/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.73/1.00  --bmc1_ucm_extend_mode                  1
% 3.73/1.00  --bmc1_ucm_init_mode                    2
% 3.73/1.00  --bmc1_ucm_cone_mode                    none
% 3.73/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.73/1.00  --bmc1_ucm_relax_model                  4
% 3.73/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.73/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.73/1.00  --bmc1_ucm_layered_model                none
% 3.73/1.00  --bmc1_ucm_max_lemma_size               10
% 3.73/1.00  
% 3.73/1.00  ------ AIG Options
% 3.73/1.00  
% 3.73/1.00  --aig_mode                              false
% 3.73/1.00  
% 3.73/1.00  ------ Instantiation Options
% 3.73/1.00  
% 3.73/1.00  --instantiation_flag                    true
% 3.73/1.00  --inst_sos_flag                         true
% 3.73/1.00  --inst_sos_phase                        true
% 3.73/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.73/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.73/1.00  --inst_lit_sel_side                     num_symb
% 3.73/1.00  --inst_solver_per_active                1400
% 3.73/1.00  --inst_solver_calls_frac                1.
% 3.73/1.00  --inst_passive_queue_type               priority_queues
% 3.73/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.73/1.00  --inst_passive_queues_freq              [25;2]
% 3.73/1.00  --inst_dismatching                      true
% 3.73/1.00  --inst_eager_unprocessed_to_passive     true
% 3.73/1.00  --inst_prop_sim_given                   true
% 3.73/1.00  --inst_prop_sim_new                     false
% 3.73/1.00  --inst_subs_new                         false
% 3.73/1.00  --inst_eq_res_simp                      false
% 3.73/1.00  --inst_subs_given                       false
% 3.73/1.00  --inst_orphan_elimination               true
% 3.73/1.00  --inst_learning_loop_flag               true
% 3.73/1.00  --inst_learning_start                   3000
% 3.73/1.00  --inst_learning_factor                  2
% 3.73/1.00  --inst_start_prop_sim_after_learn       3
% 3.73/1.00  --inst_sel_renew                        solver
% 3.73/1.00  --inst_lit_activity_flag                true
% 3.73/1.00  --inst_restr_to_given                   false
% 3.73/1.00  --inst_activity_threshold               500
% 3.73/1.00  --inst_out_proof                        true
% 3.73/1.00  
% 3.73/1.00  ------ Resolution Options
% 3.73/1.00  
% 3.73/1.00  --resolution_flag                       true
% 3.73/1.00  --res_lit_sel                           adaptive
% 3.73/1.00  --res_lit_sel_side                      none
% 3.73/1.00  --res_ordering                          kbo
% 3.73/1.00  --res_to_prop_solver                    active
% 3.73/1.00  --res_prop_simpl_new                    false
% 3.73/1.00  --res_prop_simpl_given                  true
% 3.73/1.00  --res_passive_queue_type                priority_queues
% 3.73/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.73/1.00  --res_passive_queues_freq               [15;5]
% 3.73/1.00  --res_forward_subs                      full
% 3.73/1.00  --res_backward_subs                     full
% 3.73/1.00  --res_forward_subs_resolution           true
% 3.73/1.00  --res_backward_subs_resolution          true
% 3.73/1.00  --res_orphan_elimination                true
% 3.73/1.00  --res_time_limit                        2.
% 3.73/1.00  --res_out_proof                         true
% 3.73/1.00  
% 3.73/1.00  ------ Superposition Options
% 3.73/1.00  
% 3.73/1.00  --superposition_flag                    true
% 3.73/1.00  --sup_passive_queue_type                priority_queues
% 3.73/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.73/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.73/1.00  --demod_completeness_check              fast
% 3.73/1.00  --demod_use_ground                      true
% 3.73/1.00  --sup_to_prop_solver                    passive
% 3.73/1.00  --sup_prop_simpl_new                    true
% 3.73/1.00  --sup_prop_simpl_given                  true
% 3.73/1.00  --sup_fun_splitting                     true
% 3.73/1.00  --sup_smt_interval                      50000
% 3.73/1.00  
% 3.73/1.00  ------ Superposition Simplification Setup
% 3.73/1.00  
% 3.73/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.73/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.73/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.73/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.73/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.73/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.73/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.73/1.00  --sup_immed_triv                        [TrivRules]
% 3.73/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.73/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.73/1.00  --sup_immed_bw_main                     []
% 3.73/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.73/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.73/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.73/1.00  --sup_input_bw                          []
% 3.73/1.00  
% 3.73/1.00  ------ Combination Options
% 3.73/1.00  
% 3.73/1.00  --comb_res_mult                         3
% 3.73/1.00  --comb_sup_mult                         2
% 3.73/1.00  --comb_inst_mult                        10
% 3.73/1.00  
% 3.73/1.00  ------ Debug Options
% 3.73/1.00  
% 3.73/1.00  --dbg_backtrace                         false
% 3.73/1.00  --dbg_dump_prop_clauses                 false
% 3.73/1.00  --dbg_dump_prop_clauses_file            -
% 3.73/1.00  --dbg_out_stat                          false
% 3.73/1.00  ------ Parsing...
% 3.73/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.73/1.00  
% 3.73/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.73/1.00  
% 3.73/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.73/1.00  
% 3.73/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.73/1.00  ------ Proving...
% 3.73/1.00  ------ Problem Properties 
% 3.73/1.00  
% 3.73/1.00  
% 3.73/1.00  clauses                                 33
% 3.73/1.00  conjectures                             4
% 3.73/1.00  EPR                                     4
% 3.73/1.00  Horn                                    32
% 3.73/1.00  unary                                   20
% 3.73/1.00  binary                                  7
% 3.73/1.00  lits                                    59
% 3.73/1.00  lits eq                                 25
% 3.73/1.00  fd_pure                                 0
% 3.73/1.00  fd_pseudo                               0
% 3.73/1.00  fd_cond                                 2
% 3.73/1.00  fd_pseudo_cond                          2
% 3.73/1.00  AC symbols                              0
% 3.73/1.00  
% 3.73/1.00  ------ Schedule dynamic 5 is on 
% 3.73/1.00  
% 3.73/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.73/1.00  
% 3.73/1.00  
% 3.73/1.00  ------ 
% 3.73/1.00  Current options:
% 3.73/1.00  ------ 
% 3.73/1.00  
% 3.73/1.00  ------ Input Options
% 3.73/1.00  
% 3.73/1.00  --out_options                           all
% 3.73/1.00  --tptp_safe_out                         true
% 3.73/1.00  --problem_path                          ""
% 3.73/1.00  --include_path                          ""
% 3.73/1.00  --clausifier                            res/vclausify_rel
% 3.73/1.00  --clausifier_options                    ""
% 3.73/1.00  --stdin                                 false
% 3.73/1.00  --stats_out                             all
% 3.73/1.00  
% 3.73/1.00  ------ General Options
% 3.73/1.00  
% 3.73/1.00  --fof                                   false
% 3.73/1.00  --time_out_real                         305.
% 3.73/1.00  --time_out_virtual                      -1.
% 3.73/1.00  --symbol_type_check                     false
% 3.73/1.00  --clausify_out                          false
% 3.73/1.00  --sig_cnt_out                           false
% 3.73/1.00  --trig_cnt_out                          false
% 3.73/1.00  --trig_cnt_out_tolerance                1.
% 3.73/1.00  --trig_cnt_out_sk_spl                   false
% 3.73/1.00  --abstr_cl_out                          false
% 3.73/1.00  
% 3.73/1.00  ------ Global Options
% 3.73/1.00  
% 3.73/1.00  --schedule                              default
% 3.73/1.00  --add_important_lit                     false
% 3.73/1.00  --prop_solver_per_cl                    1000
% 3.73/1.00  --min_unsat_core                        false
% 3.73/1.00  --soft_assumptions                      false
% 3.73/1.00  --soft_lemma_size                       3
% 3.73/1.00  --prop_impl_unit_size                   0
% 3.73/1.00  --prop_impl_unit                        []
% 3.73/1.00  --share_sel_clauses                     true
% 3.73/1.00  --reset_solvers                         false
% 3.73/1.00  --bc_imp_inh                            [conj_cone]
% 3.73/1.00  --conj_cone_tolerance                   3.
% 3.73/1.00  --extra_neg_conj                        none
% 3.73/1.00  --large_theory_mode                     true
% 3.73/1.00  --prolific_symb_bound                   200
% 3.73/1.00  --lt_threshold                          2000
% 3.73/1.00  --clause_weak_htbl                      true
% 3.73/1.00  --gc_record_bc_elim                     false
% 3.73/1.00  
% 3.73/1.00  ------ Preprocessing Options
% 3.73/1.00  
% 3.73/1.00  --preprocessing_flag                    true
% 3.73/1.00  --time_out_prep_mult                    0.1
% 3.73/1.00  --splitting_mode                        input
% 3.73/1.00  --splitting_grd                         true
% 3.73/1.00  --splitting_cvd                         false
% 3.73/1.00  --splitting_cvd_svl                     false
% 3.73/1.00  --splitting_nvd                         32
% 3.73/1.00  --sub_typing                            true
% 3.73/1.00  --prep_gs_sim                           true
% 3.73/1.00  --prep_unflatten                        true
% 3.73/1.00  --prep_res_sim                          true
% 3.73/1.00  --prep_upred                            true
% 3.73/1.00  --prep_sem_filter                       exhaustive
% 3.73/1.00  --prep_sem_filter_out                   false
% 3.73/1.00  --pred_elim                             true
% 3.73/1.00  --res_sim_input                         true
% 3.73/1.00  --eq_ax_congr_red                       true
% 3.73/1.00  --pure_diseq_elim                       true
% 3.73/1.00  --brand_transform                       false
% 3.73/1.00  --non_eq_to_eq                          false
% 3.73/1.00  --prep_def_merge                        true
% 3.73/1.00  --prep_def_merge_prop_impl              false
% 3.73/1.00  --prep_def_merge_mbd                    true
% 3.73/1.00  --prep_def_merge_tr_red                 false
% 3.73/1.00  --prep_def_merge_tr_cl                  false
% 3.73/1.00  --smt_preprocessing                     true
% 3.73/1.00  --smt_ac_axioms                         fast
% 3.73/1.00  --preprocessed_out                      false
% 3.73/1.00  --preprocessed_stats                    false
% 3.73/1.00  
% 3.73/1.00  ------ Abstraction refinement Options
% 3.73/1.00  
% 3.73/1.00  --abstr_ref                             []
% 3.73/1.00  --abstr_ref_prep                        false
% 3.73/1.00  --abstr_ref_until_sat                   false
% 3.73/1.00  --abstr_ref_sig_restrict                funpre
% 3.73/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.73/1.00  --abstr_ref_under                       []
% 3.73/1.00  
% 3.73/1.00  ------ SAT Options
% 3.73/1.00  
% 3.73/1.00  --sat_mode                              false
% 3.73/1.00  --sat_fm_restart_options                ""
% 3.73/1.00  --sat_gr_def                            false
% 3.73/1.00  --sat_epr_types                         true
% 3.73/1.00  --sat_non_cyclic_types                  false
% 3.73/1.00  --sat_finite_models                     false
% 3.73/1.00  --sat_fm_lemmas                         false
% 3.73/1.00  --sat_fm_prep                           false
% 3.73/1.00  --sat_fm_uc_incr                        true
% 3.73/1.00  --sat_out_model                         small
% 3.73/1.00  --sat_out_clauses                       false
% 3.73/1.00  
% 3.73/1.00  ------ QBF Options
% 3.73/1.00  
% 3.73/1.00  --qbf_mode                              false
% 3.73/1.00  --qbf_elim_univ                         false
% 3.73/1.00  --qbf_dom_inst                          none
% 3.73/1.00  --qbf_dom_pre_inst                      false
% 3.73/1.00  --qbf_sk_in                             false
% 3.73/1.00  --qbf_pred_elim                         true
% 3.73/1.00  --qbf_split                             512
% 3.73/1.00  
% 3.73/1.00  ------ BMC1 Options
% 3.73/1.00  
% 3.73/1.00  --bmc1_incremental                      false
% 3.73/1.00  --bmc1_axioms                           reachable_all
% 3.73/1.00  --bmc1_min_bound                        0
% 3.73/1.00  --bmc1_max_bound                        -1
% 3.73/1.00  --bmc1_max_bound_default                -1
% 3.73/1.00  --bmc1_symbol_reachability              true
% 3.73/1.00  --bmc1_property_lemmas                  false
% 3.73/1.00  --bmc1_k_induction                      false
% 3.73/1.00  --bmc1_non_equiv_states                 false
% 3.73/1.00  --bmc1_deadlock                         false
% 3.73/1.00  --bmc1_ucm                              false
% 3.73/1.00  --bmc1_add_unsat_core                   none
% 3.73/1.00  --bmc1_unsat_core_children              false
% 3.73/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.73/1.00  --bmc1_out_stat                         full
% 3.73/1.00  --bmc1_ground_init                      false
% 3.73/1.00  --bmc1_pre_inst_next_state              false
% 3.73/1.00  --bmc1_pre_inst_state                   false
% 3.73/1.00  --bmc1_pre_inst_reach_state             false
% 3.73/1.00  --bmc1_out_unsat_core                   false
% 3.73/1.00  --bmc1_aig_witness_out                  false
% 3.73/1.00  --bmc1_verbose                          false
% 3.73/1.00  --bmc1_dump_clauses_tptp                false
% 3.73/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.73/1.00  --bmc1_dump_file                        -
% 3.73/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.73/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.73/1.00  --bmc1_ucm_extend_mode                  1
% 3.73/1.00  --bmc1_ucm_init_mode                    2
% 3.73/1.00  --bmc1_ucm_cone_mode                    none
% 3.73/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.73/1.00  --bmc1_ucm_relax_model                  4
% 3.73/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.73/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.73/1.00  --bmc1_ucm_layered_model                none
% 3.73/1.00  --bmc1_ucm_max_lemma_size               10
% 3.73/1.00  
% 3.73/1.00  ------ AIG Options
% 3.73/1.00  
% 3.73/1.00  --aig_mode                              false
% 3.73/1.00  
% 3.73/1.00  ------ Instantiation Options
% 3.73/1.00  
% 3.73/1.00  --instantiation_flag                    true
% 3.73/1.00  --inst_sos_flag                         true
% 3.73/1.00  --inst_sos_phase                        true
% 3.73/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.73/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.73/1.00  --inst_lit_sel_side                     none
% 3.73/1.00  --inst_solver_per_active                1400
% 3.73/1.00  --inst_solver_calls_frac                1.
% 3.73/1.00  --inst_passive_queue_type               priority_queues
% 3.73/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.73/1.00  --inst_passive_queues_freq              [25;2]
% 3.73/1.00  --inst_dismatching                      true
% 3.73/1.00  --inst_eager_unprocessed_to_passive     true
% 3.73/1.00  --inst_prop_sim_given                   true
% 3.73/1.00  --inst_prop_sim_new                     false
% 3.73/1.00  --inst_subs_new                         false
% 3.73/1.00  --inst_eq_res_simp                      false
% 3.73/1.00  --inst_subs_given                       false
% 3.73/1.00  --inst_orphan_elimination               true
% 3.73/1.00  --inst_learning_loop_flag               true
% 3.73/1.00  --inst_learning_start                   3000
% 3.73/1.00  --inst_learning_factor                  2
% 3.73/1.00  --inst_start_prop_sim_after_learn       3
% 3.73/1.00  --inst_sel_renew                        solver
% 3.73/1.00  --inst_lit_activity_flag                true
% 3.73/1.00  --inst_restr_to_given                   false
% 3.73/1.00  --inst_activity_threshold               500
% 3.73/1.00  --inst_out_proof                        true
% 3.73/1.00  
% 3.73/1.00  ------ Resolution Options
% 3.73/1.00  
% 3.73/1.00  --resolution_flag                       false
% 3.73/1.00  --res_lit_sel                           adaptive
% 3.73/1.00  --res_lit_sel_side                      none
% 3.73/1.00  --res_ordering                          kbo
% 3.73/1.00  --res_to_prop_solver                    active
% 3.73/1.00  --res_prop_simpl_new                    false
% 3.73/1.00  --res_prop_simpl_given                  true
% 3.73/1.00  --res_passive_queue_type                priority_queues
% 3.73/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.73/1.00  --res_passive_queues_freq               [15;5]
% 3.73/1.00  --res_forward_subs                      full
% 3.73/1.00  --res_backward_subs                     full
% 3.73/1.00  --res_forward_subs_resolution           true
% 3.73/1.00  --res_backward_subs_resolution          true
% 3.73/1.00  --res_orphan_elimination                true
% 3.73/1.00  --res_time_limit                        2.
% 3.73/1.00  --res_out_proof                         true
% 3.73/1.00  
% 3.73/1.00  ------ Superposition Options
% 3.73/1.00  
% 3.73/1.00  --superposition_flag                    true
% 3.73/1.00  --sup_passive_queue_type                priority_queues
% 3.73/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.73/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.73/1.00  --demod_completeness_check              fast
% 3.73/1.00  --demod_use_ground                      true
% 3.73/1.00  --sup_to_prop_solver                    passive
% 3.73/1.00  --sup_prop_simpl_new                    true
% 3.73/1.00  --sup_prop_simpl_given                  true
% 3.73/1.00  --sup_fun_splitting                     true
% 3.73/1.00  --sup_smt_interval                      50000
% 3.73/1.00  
% 3.73/1.00  ------ Superposition Simplification Setup
% 3.73/1.00  
% 3.73/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.73/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.73/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.73/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.73/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.73/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.73/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.73/1.00  --sup_immed_triv                        [TrivRules]
% 3.73/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.73/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.73/1.00  --sup_immed_bw_main                     []
% 3.73/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.73/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.73/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.73/1.00  --sup_input_bw                          []
% 3.73/1.00  
% 3.73/1.00  ------ Combination Options
% 3.73/1.00  
% 3.73/1.00  --comb_res_mult                         3
% 3.73/1.00  --comb_sup_mult                         2
% 3.73/1.00  --comb_inst_mult                        10
% 3.73/1.00  
% 3.73/1.00  ------ Debug Options
% 3.73/1.00  
% 3.73/1.00  --dbg_backtrace                         false
% 3.73/1.00  --dbg_dump_prop_clauses                 false
% 3.73/1.00  --dbg_dump_prop_clauses_file            -
% 3.73/1.00  --dbg_out_stat                          false
% 3.73/1.00  
% 3.73/1.00  
% 3.73/1.00  
% 3.73/1.00  
% 3.73/1.00  ------ Proving...
% 3.73/1.00  
% 3.73/1.00  
% 3.73/1.00  % SZS status Theorem for theBenchmark.p
% 3.73/1.00  
% 3.73/1.00   Resolution empty clause
% 3.73/1.00  
% 3.73/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.73/1.00  
% 3.73/1.00  fof(f2,axiom,(
% 3.73/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.73/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.00  
% 3.73/1.00  fof(f41,plain,(
% 3.73/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.73/1.00    inference(nnf_transformation,[],[f2])).
% 3.73/1.00  
% 3.73/1.00  fof(f42,plain,(
% 3.73/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.73/1.00    inference(flattening,[],[f41])).
% 3.73/1.00  
% 3.73/1.00  fof(f53,plain,(
% 3.73/1.00    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.73/1.00    inference(cnf_transformation,[],[f42])).
% 3.73/1.00  
% 3.73/1.00  fof(f115,plain,(
% 3.73/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.73/1.00    inference(equality_resolution,[],[f53])).
% 3.73/1.00  
% 3.73/1.00  fof(f21,conjecture,(
% 3.73/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 3.73/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.00  
% 3.73/1.00  fof(f22,negated_conjecture,(
% 3.73/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 3.73/1.00    inference(negated_conjecture,[],[f21])).
% 3.73/1.00  
% 3.73/1.00  fof(f39,plain,(
% 3.73/1.00    ? [X0,X1,X2] : ((k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 3.73/1.00    inference(ennf_transformation,[],[f22])).
% 3.73/1.00  
% 3.73/1.00  fof(f40,plain,(
% 3.73/1.00    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 3.73/1.00    inference(flattening,[],[f39])).
% 3.73/1.00  
% 3.73/1.00  fof(f49,plain,(
% 3.73/1.00    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_tarski(k1_funct_1(sK3,sK1)) != k2_relset_1(k1_tarski(sK1),sK2,sK3) & k1_xboole_0 != sK2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK3,k1_tarski(sK1),sK2) & v1_funct_1(sK3))),
% 3.73/1.00    introduced(choice_axiom,[])).
% 3.73/1.00  
% 3.73/1.00  fof(f50,plain,(
% 3.73/1.00    k1_tarski(k1_funct_1(sK3,sK1)) != k2_relset_1(k1_tarski(sK1),sK2,sK3) & k1_xboole_0 != sK2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK3,k1_tarski(sK1),sK2) & v1_funct_1(sK3)),
% 3.73/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f40,f49])).
% 3.73/1.00  
% 3.73/1.00  fof(f89,plain,(
% 3.73/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))),
% 3.73/1.00    inference(cnf_transformation,[],[f50])).
% 3.73/1.00  
% 3.73/1.00  fof(f3,axiom,(
% 3.73/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.73/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.00  
% 3.73/1.00  fof(f55,plain,(
% 3.73/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.73/1.00    inference(cnf_transformation,[],[f3])).
% 3.73/1.00  
% 3.73/1.00  fof(f4,axiom,(
% 3.73/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.73/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.00  
% 3.73/1.00  fof(f56,plain,(
% 3.73/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.73/1.00    inference(cnf_transformation,[],[f4])).
% 3.73/1.00  
% 3.73/1.00  fof(f5,axiom,(
% 3.73/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.73/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.00  
% 3.73/1.00  fof(f57,plain,(
% 3.73/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.73/1.00    inference(cnf_transformation,[],[f5])).
% 3.73/1.00  
% 3.73/1.00  fof(f92,plain,(
% 3.73/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.73/1.00    inference(definition_unfolding,[],[f56,f57])).
% 3.73/1.00  
% 3.73/1.00  fof(f93,plain,(
% 3.73/1.00    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.73/1.00    inference(definition_unfolding,[],[f55,f92])).
% 3.73/1.00  
% 3.73/1.00  fof(f113,plain,(
% 3.73/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))),
% 3.73/1.00    inference(definition_unfolding,[],[f89,f93])).
% 3.73/1.00  
% 3.73/1.00  fof(f18,axiom,(
% 3.73/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 3.73/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.00  
% 3.73/1.00  fof(f36,plain,(
% 3.73/1.00    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.73/1.00    inference(ennf_transformation,[],[f18])).
% 3.73/1.00  
% 3.73/1.00  fof(f81,plain,(
% 3.73/1.00    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.73/1.00    inference(cnf_transformation,[],[f36])).
% 3.73/1.00  
% 3.73/1.00  fof(f20,axiom,(
% 3.73/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,X1) = X0))),
% 3.73/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.00  
% 3.73/1.00  fof(f37,plain,(
% 3.73/1.00    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.73/1.00    inference(ennf_transformation,[],[f20])).
% 3.73/1.00  
% 3.73/1.00  fof(f38,plain,(
% 3.73/1.00    ! [X0,X1,X2] : (k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.73/1.00    inference(flattening,[],[f37])).
% 3.73/1.00  
% 3.73/1.00  fof(f85,plain,(
% 3.73/1.00    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.73/1.00    inference(cnf_transformation,[],[f38])).
% 3.73/1.00  
% 3.73/1.00  fof(f1,axiom,(
% 3.73/1.00    k1_xboole_0 = o_0_0_xboole_0),
% 3.73/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.00  
% 3.73/1.00  fof(f51,plain,(
% 3.73/1.00    k1_xboole_0 = o_0_0_xboole_0),
% 3.73/1.00    inference(cnf_transformation,[],[f1])).
% 3.73/1.00  
% 3.73/1.00  fof(f110,plain,(
% 3.73/1.00    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = X0 | o_0_0_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.73/1.00    inference(definition_unfolding,[],[f85,f51])).
% 3.73/1.00  
% 3.73/1.00  fof(f88,plain,(
% 3.73/1.00    v1_funct_2(sK3,k1_tarski(sK1),sK2)),
% 3.73/1.00    inference(cnf_transformation,[],[f50])).
% 3.73/1.00  
% 3.73/1.00  fof(f114,plain,(
% 3.73/1.00    v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2)),
% 3.73/1.00    inference(definition_unfolding,[],[f88,f93])).
% 3.73/1.00  
% 3.73/1.00  fof(f87,plain,(
% 3.73/1.00    v1_funct_1(sK3)),
% 3.73/1.00    inference(cnf_transformation,[],[f50])).
% 3.73/1.00  
% 3.73/1.00  fof(f90,plain,(
% 3.73/1.00    k1_xboole_0 != sK2),
% 3.73/1.00    inference(cnf_transformation,[],[f50])).
% 3.73/1.00  
% 3.73/1.00  fof(f112,plain,(
% 3.73/1.00    o_0_0_xboole_0 != sK2),
% 3.73/1.00    inference(definition_unfolding,[],[f90,f51])).
% 3.73/1.00  
% 3.73/1.00  fof(f15,axiom,(
% 3.73/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.73/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.00  
% 3.73/1.00  fof(f23,plain,(
% 3.73/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.73/1.00    inference(pure_predicate_removal,[],[f15])).
% 3.73/1.00  
% 3.73/1.00  fof(f33,plain,(
% 3.73/1.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.73/1.00    inference(ennf_transformation,[],[f23])).
% 3.73/1.00  
% 3.73/1.00  fof(f78,plain,(
% 3.73/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.73/1.00    inference(cnf_transformation,[],[f33])).
% 3.73/1.00  
% 3.73/1.00  fof(f10,axiom,(
% 3.73/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.73/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.00  
% 3.73/1.00  fof(f27,plain,(
% 3.73/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.73/1.00    inference(ennf_transformation,[],[f10])).
% 3.73/1.00  
% 3.73/1.00  fof(f46,plain,(
% 3.73/1.00    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.73/1.00    inference(nnf_transformation,[],[f27])).
% 3.73/1.00  
% 3.73/1.00  fof(f70,plain,(
% 3.73/1.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.73/1.00    inference(cnf_transformation,[],[f46])).
% 3.73/1.00  
% 3.73/1.00  fof(f14,axiom,(
% 3.73/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.73/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.00  
% 3.73/1.00  fof(f32,plain,(
% 3.73/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.73/1.00    inference(ennf_transformation,[],[f14])).
% 3.73/1.00  
% 3.73/1.00  fof(f77,plain,(
% 3.73/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.73/1.00    inference(cnf_transformation,[],[f32])).
% 3.73/1.00  
% 3.73/1.00  fof(f6,axiom,(
% 3.73/1.00    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> ~(k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3))),
% 3.73/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.00  
% 3.73/1.00  fof(f26,plain,(
% 3.73/1.00    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3))),
% 3.73/1.00    inference(ennf_transformation,[],[f6])).
% 3.73/1.00  
% 3.73/1.00  fof(f43,plain,(
% 3.73/1.00    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & ((k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3) | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 3.73/1.00    inference(nnf_transformation,[],[f26])).
% 3.73/1.00  
% 3.73/1.00  fof(f44,plain,(
% 3.73/1.00    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 3.73/1.00    inference(flattening,[],[f43])).
% 3.73/1.00  
% 3.73/1.00  fof(f58,plain,(
% 3.73/1.00    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))) )),
% 3.73/1.00    inference(cnf_transformation,[],[f44])).
% 3.73/1.00  
% 3.73/1.00  fof(f102,plain,(
% 3.73/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X0,X1,X2) = X3 | k2_enumset1(X0,X0,X0,X2) = X3 | k2_enumset1(X1,X1,X1,X2) = X3 | k2_enumset1(X0,X0,X0,X1) = X3 | k2_enumset1(X2,X2,X2,X2) = X3 | k2_enumset1(X1,X1,X1,X1) = X3 | k2_enumset1(X0,X0,X0,X0) = X3 | o_0_0_xboole_0 = X3 | ~r1_tarski(X3,k2_enumset1(X0,X0,X1,X2))) )),
% 3.73/1.00    inference(definition_unfolding,[],[f58,f57,f92,f92,f92,f93,f93,f93,f51,f57])).
% 3.73/1.00  
% 3.73/1.00  fof(f54,plain,(
% 3.73/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.73/1.00    inference(cnf_transformation,[],[f42])).
% 3.73/1.00  
% 3.73/1.00  fof(f91,plain,(
% 3.73/1.00    k1_tarski(k1_funct_1(sK3,sK1)) != k2_relset_1(k1_tarski(sK1),sK2,sK3)),
% 3.73/1.00    inference(cnf_transformation,[],[f50])).
% 3.73/1.00  
% 3.73/1.00  fof(f111,plain,(
% 3.73/1.00    k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3)),
% 3.73/1.00    inference(definition_unfolding,[],[f91,f93,f93])).
% 3.73/1.00  
% 3.73/1.00  fof(f17,axiom,(
% 3.73/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.73/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.00  
% 3.73/1.00  fof(f35,plain,(
% 3.73/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.73/1.00    inference(ennf_transformation,[],[f17])).
% 3.73/1.00  
% 3.73/1.00  fof(f80,plain,(
% 3.73/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.73/1.00    inference(cnf_transformation,[],[f35])).
% 3.73/1.00  
% 3.73/1.00  fof(f13,axiom,(
% 3.73/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 3.73/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.00  
% 3.73/1.00  fof(f30,plain,(
% 3.73/1.00    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.73/1.00    inference(ennf_transformation,[],[f13])).
% 3.73/1.00  
% 3.73/1.00  fof(f31,plain,(
% 3.73/1.00    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.73/1.00    inference(flattening,[],[f30])).
% 3.73/1.00  
% 3.73/1.00  fof(f76,plain,(
% 3.73/1.00    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.73/1.00    inference(cnf_transformation,[],[f31])).
% 3.73/1.00  
% 3.73/1.00  fof(f108,plain,(
% 3.73/1.00    ( ! [X0,X1] : (k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1) | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.73/1.00    inference(definition_unfolding,[],[f76,f93,f93])).
% 3.73/1.00  
% 3.73/1.00  fof(f12,axiom,(
% 3.73/1.00    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 3.73/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.00  
% 3.73/1.00  fof(f28,plain,(
% 3.73/1.00    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.73/1.00    inference(ennf_transformation,[],[f12])).
% 3.73/1.00  
% 3.73/1.00  fof(f29,plain,(
% 3.73/1.00    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.73/1.00    inference(flattening,[],[f28])).
% 3.73/1.00  
% 3.73/1.00  fof(f74,plain,(
% 3.73/1.00    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.73/1.00    inference(cnf_transformation,[],[f29])).
% 3.73/1.00  
% 3.73/1.00  fof(f107,plain,(
% 3.73/1.00    ( ! [X0] : (o_0_0_xboole_0 = X0 | o_0_0_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.73/1.00    inference(definition_unfolding,[],[f74,f51,f51])).
% 3.73/1.00  
% 3.73/1.00  fof(f19,axiom,(
% 3.73/1.00    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_tarski(X2) = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 3.73/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.00  
% 3.73/1.00  fof(f24,plain,(
% 3.73/1.00    ! [X0] : ? [X1] : (k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 3.73/1.00    inference(pure_predicate_removal,[],[f19])).
% 3.73/1.00  
% 3.73/1.00  fof(f47,plain,(
% 3.73/1.00    ! [X0] : (? [X1] : (k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (k1_relat_1(sK0(X0)) = X0 & v1_funct_1(sK0(X0)) & v1_relat_1(sK0(X0))))),
% 3.73/1.00    introduced(choice_axiom,[])).
% 3.73/1.00  
% 3.73/1.00  fof(f48,plain,(
% 3.73/1.00    ! [X0] : (k1_relat_1(sK0(X0)) = X0 & v1_funct_1(sK0(X0)) & v1_relat_1(sK0(X0)))),
% 3.73/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f47])).
% 3.73/1.00  
% 3.73/1.00  fof(f84,plain,(
% 3.73/1.00    ( ! [X0] : (k1_relat_1(sK0(X0)) = X0) )),
% 3.73/1.00    inference(cnf_transformation,[],[f48])).
% 3.73/1.00  
% 3.73/1.00  fof(f82,plain,(
% 3.73/1.00    ( ! [X0] : (v1_relat_1(sK0(X0))) )),
% 3.73/1.00    inference(cnf_transformation,[],[f48])).
% 3.73/1.00  
% 3.73/1.00  fof(f83,plain,(
% 3.73/1.00    ( ! [X0] : (v1_funct_1(sK0(X0))) )),
% 3.73/1.00    inference(cnf_transformation,[],[f48])).
% 3.73/1.00  
% 3.73/1.00  fof(f11,axiom,(
% 3.73/1.00    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.73/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.00  
% 3.73/1.00  fof(f73,plain,(
% 3.73/1.00    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 3.73/1.00    inference(cnf_transformation,[],[f11])).
% 3.73/1.00  
% 3.73/1.00  fof(f104,plain,(
% 3.73/1.00    o_0_0_xboole_0 = k2_relat_1(o_0_0_xboole_0)),
% 3.73/1.00    inference(definition_unfolding,[],[f73,f51,f51])).
% 3.73/1.00  
% 3.73/1.00  fof(f7,axiom,(
% 3.73/1.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.73/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.00  
% 3.73/1.00  fof(f67,plain,(
% 3.73/1.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.73/1.00    inference(cnf_transformation,[],[f7])).
% 3.73/1.00  
% 3.73/1.00  fof(f103,plain,(
% 3.73/1.00    ( ! [X0] : (m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0))) )),
% 3.73/1.00    inference(definition_unfolding,[],[f67,f51])).
% 3.73/1.00  
% 3.73/1.00  fof(f16,axiom,(
% 3.73/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)))),
% 3.73/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.00  
% 3.73/1.00  fof(f34,plain,(
% 3.73/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.73/1.00    inference(ennf_transformation,[],[f16])).
% 3.73/1.00  
% 3.73/1.00  fof(f79,plain,(
% 3.73/1.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.73/1.00    inference(cnf_transformation,[],[f34])).
% 3.73/1.00  
% 3.73/1.00  fof(f8,axiom,(
% 3.73/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.73/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.00  
% 3.73/1.00  fof(f45,plain,(
% 3.73/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.73/1.00    inference(nnf_transformation,[],[f8])).
% 3.73/1.00  
% 3.73/1.00  fof(f68,plain,(
% 3.73/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.73/1.00    inference(cnf_transformation,[],[f45])).
% 3.73/1.00  
% 3.73/1.00  fof(f72,plain,(
% 3.73/1.00    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.73/1.00    inference(cnf_transformation,[],[f11])).
% 3.73/1.00  
% 3.73/1.00  fof(f105,plain,(
% 3.73/1.00    o_0_0_xboole_0 = k1_relat_1(o_0_0_xboole_0)),
% 3.73/1.00    inference(definition_unfolding,[],[f72,f51,f51])).
% 3.73/1.00  
% 3.73/1.00  cnf(c_1,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f115]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_1574,plain,
% 3.73/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 3.73/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_34,negated_conjecture,
% 3.73/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
% 3.73/1.00      inference(cnf_transformation,[],[f113]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_1552,plain,
% 3.73/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) = iProver_top ),
% 3.73/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_26,plain,
% 3.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.73/1.00      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 3.73/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_1555,plain,
% 3.73/1.00      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 3.73/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.73/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_3811,plain,
% 3.73/1.00      ( k8_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3,X0) = k10_relat_1(sK3,X0) ),
% 3.73/1.00      inference(superposition,[status(thm)],[c_1552,c_1555]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_31,plain,
% 3.73/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.73/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.73/1.00      | ~ v1_funct_1(X0)
% 3.73/1.00      | k8_relset_1(X1,X2,X0,X2) = X1
% 3.73/1.00      | o_0_0_xboole_0 = X2 ),
% 3.73/1.00      inference(cnf_transformation,[],[f110]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_35,negated_conjecture,
% 3.73/1.00      ( v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
% 3.73/1.00      inference(cnf_transformation,[],[f114]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_457,plain,
% 3.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.73/1.00      | ~ v1_funct_1(X0)
% 3.73/1.00      | k8_relset_1(X1,X2,X0,X2) = X1
% 3.73/1.00      | k2_enumset1(sK1,sK1,sK1,sK1) != X1
% 3.73/1.00      | sK2 != X2
% 3.73/1.00      | sK3 != X0
% 3.73/1.00      | o_0_0_xboole_0 = X2 ),
% 3.73/1.00      inference(resolution_lifted,[status(thm)],[c_31,c_35]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_458,plain,
% 3.73/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))
% 3.73/1.00      | ~ v1_funct_1(sK3)
% 3.73/1.00      | k8_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3,sK2) = k2_enumset1(sK1,sK1,sK1,sK1)
% 3.73/1.00      | o_0_0_xboole_0 = sK2 ),
% 3.73/1.00      inference(unflattening,[status(thm)],[c_457]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_36,negated_conjecture,
% 3.73/1.00      ( v1_funct_1(sK3) ),
% 3.73/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_33,negated_conjecture,
% 3.73/1.00      ( o_0_0_xboole_0 != sK2 ),
% 3.73/1.00      inference(cnf_transformation,[],[f112]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_460,plain,
% 3.73/1.00      ( k8_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3,sK2) = k2_enumset1(sK1,sK1,sK1,sK1) ),
% 3.73/1.00      inference(global_propositional_subsumption,
% 3.73/1.00                [status(thm)],
% 3.73/1.00                [c_458,c_36,c_34,c_33]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_4051,plain,
% 3.73/1.00      ( k2_enumset1(sK1,sK1,sK1,sK1) = k10_relat_1(sK3,sK2) ),
% 3.73/1.00      inference(demodulation,[status(thm)],[c_3811,c_460]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_23,plain,
% 3.73/1.00      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.73/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_16,plain,
% 3.73/1.00      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 3.73/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_419,plain,
% 3.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.73/1.00      | r1_tarski(k1_relat_1(X0),X1)
% 3.73/1.00      | ~ v1_relat_1(X0) ),
% 3.73/1.00      inference(resolution,[status(thm)],[c_23,c_16]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_22,plain,
% 3.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.73/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_423,plain,
% 3.73/1.00      ( r1_tarski(k1_relat_1(X0),X1)
% 3.73/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.73/1.00      inference(global_propositional_subsumption,[status(thm)],[c_419,c_22]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_424,plain,
% 3.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.73/1.00      | r1_tarski(k1_relat_1(X0),X1) ),
% 3.73/1.00      inference(renaming,[status(thm)],[c_423]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_1550,plain,
% 3.73/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.73/1.00      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 3.73/1.00      inference(predicate_to_equality,[status(thm)],[c_424]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_2047,plain,
% 3.73/1.00      ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK1,sK1,sK1,sK1)) = iProver_top ),
% 3.73/1.00      inference(superposition,[status(thm)],[c_1552,c_1550]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_4066,plain,
% 3.73/1.00      ( r1_tarski(k1_relat_1(sK3),k10_relat_1(sK3,sK2)) = iProver_top ),
% 3.73/1.00      inference(demodulation,[status(thm)],[c_4051,c_2047]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_11,plain,
% 3.73/1.00      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X2,X3))
% 3.73/1.00      | k2_enumset1(X1,X1,X2,X3) = X0
% 3.73/1.00      | k2_enumset1(X1,X1,X1,X3) = X0
% 3.73/1.00      | k2_enumset1(X2,X2,X2,X3) = X0
% 3.73/1.00      | k2_enumset1(X1,X1,X1,X2) = X0
% 3.73/1.00      | k2_enumset1(X3,X3,X3,X3) = X0
% 3.73/1.00      | k2_enumset1(X2,X2,X2,X2) = X0
% 3.73/1.00      | k2_enumset1(X1,X1,X1,X1) = X0
% 3.73/1.00      | o_0_0_xboole_0 = X0 ),
% 3.73/1.00      inference(cnf_transformation,[],[f102]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_1565,plain,
% 3.73/1.00      ( k2_enumset1(X0,X0,X1,X2) = X3
% 3.73/1.00      | k2_enumset1(X0,X0,X0,X2) = X3
% 3.73/1.00      | k2_enumset1(X1,X1,X1,X2) = X3
% 3.73/1.00      | k2_enumset1(X0,X0,X0,X1) = X3
% 3.73/1.00      | k2_enumset1(X2,X2,X2,X2) = X3
% 3.73/1.00      | k2_enumset1(X1,X1,X1,X1) = X3
% 3.73/1.00      | k2_enumset1(X0,X0,X0,X0) = X3
% 3.73/1.00      | o_0_0_xboole_0 = X3
% 3.73/1.00      | r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) != iProver_top ),
% 3.73/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_4729,plain,
% 3.73/1.00      ( k2_enumset1(sK1,sK1,sK1,sK1) = X0
% 3.73/1.00      | o_0_0_xboole_0 = X0
% 3.73/1.00      | r1_tarski(X0,k10_relat_1(sK3,sK2)) != iProver_top ),
% 3.73/1.00      inference(superposition,[status(thm)],[c_4051,c_1565]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_4730,plain,
% 3.73/1.00      ( k10_relat_1(sK3,sK2) = X0
% 3.73/1.00      | o_0_0_xboole_0 = X0
% 3.73/1.00      | r1_tarski(X0,k10_relat_1(sK3,sK2)) != iProver_top ),
% 3.73/1.00      inference(demodulation,[status(thm)],[c_4729,c_4051]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_5641,plain,
% 3.73/1.00      ( k10_relat_1(sK3,sK2) = k1_relat_1(sK3)
% 3.73/1.00      | k1_relat_1(sK3) = o_0_0_xboole_0 ),
% 3.73/1.00      inference(superposition,[status(thm)],[c_4066,c_4730]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_0,plain,
% 3.73/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.73/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_1575,plain,
% 3.73/1.00      ( X0 = X1
% 3.73/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.73/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.73/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_3784,plain,
% 3.73/1.00      ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3)
% 3.73/1.00      | r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k1_relat_1(sK3)) != iProver_top ),
% 3.73/1.00      inference(superposition,[status(thm)],[c_2047,c_1575]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_32,negated_conjecture,
% 3.73/1.00      ( k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) ),
% 3.73/1.00      inference(cnf_transformation,[],[f111]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_947,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_1608,plain,
% 3.73/1.00      ( k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != X0
% 3.73/1.00      | k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) = k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3)
% 3.73/1.00      | k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) != X0 ),
% 3.73/1.00      inference(instantiation,[status(thm)],[c_947]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_1674,plain,
% 3.73/1.00      ( k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) = k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3)
% 3.73/1.00      | k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relat_1(sK3)
% 3.73/1.00      | k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) != k2_relat_1(sK3) ),
% 3.73/1.00      inference(instantiation,[status(thm)],[c_1608]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_25,plain,
% 3.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.73/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.73/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_1746,plain,
% 3.73/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))
% 3.73/1.00      | k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) = k2_relat_1(sK3) ),
% 3.73/1.00      inference(instantiation,[status(thm)],[c_25]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_21,plain,
% 3.73/1.00      ( ~ v1_funct_1(X0)
% 3.73/1.00      | ~ v1_relat_1(X0)
% 3.73/1.00      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 3.73/1.00      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
% 3.73/1.00      inference(cnf_transformation,[],[f108]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_1934,plain,
% 3.73/1.00      ( ~ v1_funct_1(sK3)
% 3.73/1.00      | ~ v1_relat_1(sK3)
% 3.73/1.00      | k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) = k2_relat_1(sK3)
% 3.73/1.00      | k2_enumset1(sK1,sK1,sK1,sK1) != k1_relat_1(sK3) ),
% 3.73/1.00      inference(instantiation,[status(thm)],[c_21]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_2072,plain,
% 3.73/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))
% 3.73/1.00      | v1_relat_1(sK3) ),
% 3.73/1.00      inference(instantiation,[status(thm)],[c_22]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_2305,plain,
% 3.73/1.00      ( ~ r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k1_relat_1(sK3))
% 3.73/1.00      | ~ r1_tarski(k1_relat_1(sK3),k2_enumset1(sK1,sK1,sK1,sK1))
% 3.73/1.00      | k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3) ),
% 3.73/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_2306,plain,
% 3.73/1.00      ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3)
% 3.73/1.00      | r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k1_relat_1(sK3)) != iProver_top
% 3.73/1.00      | r1_tarski(k1_relat_1(sK3),k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top ),
% 3.73/1.00      inference(predicate_to_equality,[status(thm)],[c_2305]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_5080,plain,
% 3.73/1.00      ( r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k1_relat_1(sK3)) != iProver_top ),
% 3.73/1.00      inference(global_propositional_subsumption,
% 3.73/1.00                [status(thm)],
% 3.73/1.00                [c_3784,c_36,c_34,c_32,c_1674,c_1746,c_1934,c_2047,c_2072,
% 3.73/1.00                 c_2306]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_5084,plain,
% 3.73/1.00      ( r1_tarski(k10_relat_1(sK3,sK2),k1_relat_1(sK3)) != iProver_top ),
% 3.73/1.00      inference(light_normalisation,[status(thm)],[c_5080,c_4051]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_6345,plain,
% 3.73/1.00      ( k1_relat_1(sK3) = o_0_0_xboole_0
% 3.73/1.00      | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) != iProver_top ),
% 3.73/1.00      inference(superposition,[status(thm)],[c_5641,c_5084]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_6466,plain,
% 3.73/1.00      ( k1_relat_1(sK3) = o_0_0_xboole_0 ),
% 3.73/1.00      inference(superposition,[status(thm)],[c_1574,c_6345]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_20,plain,
% 3.73/1.00      ( ~ v1_relat_1(X0)
% 3.73/1.00      | k1_relat_1(X0) != o_0_0_xboole_0
% 3.73/1.00      | o_0_0_xboole_0 = X0 ),
% 3.73/1.00      inference(cnf_transformation,[],[f107]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_1560,plain,
% 3.73/1.00      ( k1_relat_1(X0) != o_0_0_xboole_0
% 3.73/1.00      | o_0_0_xboole_0 = X0
% 3.73/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.73/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_6759,plain,
% 3.73/1.00      ( sK3 = o_0_0_xboole_0 | v1_relat_1(sK3) != iProver_top ),
% 3.73/1.00      inference(superposition,[status(thm)],[c_6466,c_1560]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_946,plain,( X0 = X0 ),theory(equality) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_1838,plain,
% 3.73/1.00      ( sK3 = sK3 ),
% 3.73/1.00      inference(instantiation,[status(thm)],[c_946]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_1714,plain,
% 3.73/1.00      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 3.73/1.00      inference(instantiation,[status(thm)],[c_947]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_1892,plain,
% 3.73/1.00      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 3.73/1.00      inference(instantiation,[status(thm)],[c_1714]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_1893,plain,
% 3.73/1.00      ( sK3 != sK3 | sK3 = o_0_0_xboole_0 | o_0_0_xboole_0 != sK3 ),
% 3.73/1.00      inference(instantiation,[status(thm)],[c_1892]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_2842,plain,
% 3.73/1.00      ( ~ v1_relat_1(sK3)
% 3.73/1.00      | k1_relat_1(sK3) != o_0_0_xboole_0
% 3.73/1.00      | o_0_0_xboole_0 = sK3 ),
% 3.73/1.00      inference(instantiation,[status(thm)],[c_20]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_6925,plain,
% 3.73/1.00      ( sK3 = o_0_0_xboole_0 ),
% 3.73/1.00      inference(global_propositional_subsumption,
% 3.73/1.00                [status(thm)],
% 3.73/1.00                [c_6759,c_34,c_1838,c_1893,c_2072,c_2842,c_6466]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_27,plain,
% 3.73/1.00      ( k1_relat_1(sK0(X0)) = X0 ),
% 3.73/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_1559,plain,
% 3.73/1.00      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1)
% 3.73/1.00      | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
% 3.73/1.00      | v1_funct_1(X1) != iProver_top
% 3.73/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.73/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_3911,plain,
% 3.73/1.00      ( k2_enumset1(X0,X0,X0,X0) != X1
% 3.73/1.00      | k2_enumset1(k1_funct_1(sK0(X1),X0),k1_funct_1(sK0(X1),X0),k1_funct_1(sK0(X1),X0),k1_funct_1(sK0(X1),X0)) = k2_relat_1(sK0(X1))
% 3.73/1.00      | v1_funct_1(sK0(X1)) != iProver_top
% 3.73/1.00      | v1_relat_1(sK0(X1)) != iProver_top ),
% 3.73/1.00      inference(superposition,[status(thm)],[c_27,c_1559]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_4082,plain,
% 3.73/1.00      ( k2_enumset1(k1_funct_1(sK0(X0),sK1),k1_funct_1(sK0(X0),sK1),k1_funct_1(sK0(X0),sK1),k1_funct_1(sK0(X0),sK1)) = k2_relat_1(sK0(X0))
% 3.73/1.00      | k10_relat_1(sK3,sK2) != X0
% 3.73/1.00      | v1_funct_1(sK0(X0)) != iProver_top
% 3.73/1.00      | v1_relat_1(sK0(X0)) != iProver_top ),
% 3.73/1.00      inference(superposition,[status(thm)],[c_4051,c_3911]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_29,plain,
% 3.73/1.00      ( v1_relat_1(sK0(X0)) ),
% 3.73/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_28,plain,
% 3.73/1.00      ( v1_funct_1(sK0(X0)) ),
% 3.73/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_4090,plain,
% 3.73/1.00      ( ~ v1_funct_1(sK0(X0))
% 3.73/1.00      | ~ v1_relat_1(sK0(X0))
% 3.73/1.00      | k2_enumset1(k1_funct_1(sK0(X0),sK1),k1_funct_1(sK0(X0),sK1),k1_funct_1(sK0(X0),sK1),k1_funct_1(sK0(X0),sK1)) = k2_relat_1(sK0(X0))
% 3.73/1.00      | k10_relat_1(sK3,sK2) != X0 ),
% 3.73/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_4082]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_5629,plain,
% 3.73/1.00      ( k2_enumset1(k1_funct_1(sK0(X0),sK1),k1_funct_1(sK0(X0),sK1),k1_funct_1(sK0(X0),sK1),k1_funct_1(sK0(X0),sK1)) = k2_relat_1(sK0(X0))
% 3.73/1.00      | k10_relat_1(sK3,sK2) != X0 ),
% 3.73/1.00      inference(global_propositional_subsumption,
% 3.73/1.00                [status(thm)],
% 3.73/1.00                [c_4082,c_29,c_28,c_4090]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_5632,plain,
% 3.73/1.00      ( k2_enumset1(k1_funct_1(sK0(k10_relat_1(sK3,sK2)),sK1),k1_funct_1(sK0(k10_relat_1(sK3,sK2)),sK1),k1_funct_1(sK0(k10_relat_1(sK3,sK2)),sK1),k1_funct_1(sK0(k10_relat_1(sK3,sK2)),sK1)) = k2_relat_1(sK0(k10_relat_1(sK3,sK2))) ),
% 3.73/1.00      inference(equality_resolution,[status(thm)],[c_5629]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_6930,plain,
% 3.73/1.00      ( k2_enumset1(k1_funct_1(sK0(k10_relat_1(o_0_0_xboole_0,sK2)),sK1),k1_funct_1(sK0(k10_relat_1(o_0_0_xboole_0,sK2)),sK1),k1_funct_1(sK0(k10_relat_1(o_0_0_xboole_0,sK2)),sK1),k1_funct_1(sK0(k10_relat_1(o_0_0_xboole_0,sK2)),sK1)) = k2_relat_1(sK0(k10_relat_1(o_0_0_xboole_0,sK2))) ),
% 3.73/1.00      inference(demodulation,[status(thm)],[c_6925,c_5632]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_17,plain,
% 3.73/1.00      ( k2_relat_1(o_0_0_xboole_0) = o_0_0_xboole_0 ),
% 3.73/1.00      inference(cnf_transformation,[],[f104]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_3091,plain,
% 3.73/1.00      ( sK0(X0) = o_0_0_xboole_0
% 3.73/1.00      | o_0_0_xboole_0 != X0
% 3.73/1.00      | v1_relat_1(sK0(X0)) != iProver_top ),
% 3.73/1.00      inference(superposition,[status(thm)],[c_27,c_1560]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_46,plain,
% 3.73/1.00      ( v1_relat_1(sK0(X0)) = iProver_top ),
% 3.73/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_3176,plain,
% 3.73/1.00      ( o_0_0_xboole_0 != X0 | sK0(X0) = o_0_0_xboole_0 ),
% 3.73/1.00      inference(global_propositional_subsumption,[status(thm)],[c_3091,c_46]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_3177,plain,
% 3.73/1.00      ( sK0(X0) = o_0_0_xboole_0 | o_0_0_xboole_0 != X0 ),
% 3.73/1.00      inference(renaming,[status(thm)],[c_3176]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_3179,plain,
% 3.73/1.00      ( sK0(o_0_0_xboole_0) = o_0_0_xboole_0 ),
% 3.73/1.00      inference(equality_resolution,[status(thm)],[c_3177]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_12,plain,
% 3.73/1.00      ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0)) ),
% 3.73/1.00      inference(cnf_transformation,[],[f103]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_1564,plain,
% 3.73/1.00      ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.73/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_3808,plain,
% 3.73/1.00      ( k8_relset_1(X0,X1,o_0_0_xboole_0,X2) = k10_relat_1(o_0_0_xboole_0,X2) ),
% 3.73/1.00      inference(superposition,[status(thm)],[c_1564,c_1555]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_24,plain,
% 3.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.73/1.00      | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) ),
% 3.73/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_1557,plain,
% 3.73/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.73/1.00      | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) = iProver_top ),
% 3.73/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_4828,plain,
% 3.73/1.00      ( m1_subset_1(k10_relat_1(o_0_0_xboole_0,X0),k1_zfmisc_1(X1)) = iProver_top
% 3.73/1.00      | m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 3.73/1.00      inference(superposition,[status(thm)],[c_3808,c_1557]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_6270,plain,
% 3.73/1.00      ( m1_subset_1(k10_relat_1(o_0_0_xboole_0,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 3.73/1.00      inference(superposition,[status(thm)],[c_1564,c_4828]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_14,plain,
% 3.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.73/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_1562,plain,
% 3.73/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.73/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.73/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_6762,plain,
% 3.73/1.00      ( r1_tarski(k10_relat_1(o_0_0_xboole_0,X0),X1) = iProver_top ),
% 3.73/1.00      inference(superposition,[status(thm)],[c_6270,c_1562]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_2295,plain,
% 3.73/1.00      ( r1_tarski(k1_relat_1(o_0_0_xboole_0),X0) = iProver_top ),
% 3.73/1.00      inference(superposition,[status(thm)],[c_1564,c_1550]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_18,plain,
% 3.73/1.00      ( k1_relat_1(o_0_0_xboole_0) = o_0_0_xboole_0 ),
% 3.73/1.00      inference(cnf_transformation,[],[f105]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_2296,plain,
% 3.73/1.00      ( r1_tarski(o_0_0_xboole_0,X0) = iProver_top ),
% 3.73/1.00      inference(light_normalisation,[status(thm)],[c_2295,c_18]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_3781,plain,
% 3.73/1.00      ( o_0_0_xboole_0 = X0 | r1_tarski(X0,o_0_0_xboole_0) != iProver_top ),
% 3.73/1.00      inference(superposition,[status(thm)],[c_2296,c_1575]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_6917,plain,
% 3.73/1.00      ( k10_relat_1(o_0_0_xboole_0,X0) = o_0_0_xboole_0 ),
% 3.73/1.00      inference(superposition,[status(thm)],[c_6762,c_3781]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_6978,plain,
% 3.73/1.00      ( k2_enumset1(k1_funct_1(o_0_0_xboole_0,sK1),k1_funct_1(o_0_0_xboole_0,sK1),k1_funct_1(o_0_0_xboole_0,sK1),k1_funct_1(o_0_0_xboole_0,sK1)) = o_0_0_xboole_0 ),
% 3.73/1.00      inference(demodulation,[status(thm)],[c_6930,c_17,c_3179,c_6917]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_1556,plain,
% 3.73/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.73/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.73/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_3184,plain,
% 3.73/1.00      ( k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) = k2_relat_1(sK3) ),
% 3.73/1.00      inference(superposition,[status(thm)],[c_1552,c_1556]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_3261,plain,
% 3.73/1.00      ( k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relat_1(sK3) ),
% 3.73/1.00      inference(demodulation,[status(thm)],[c_3184,c_32]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_6950,plain,
% 3.73/1.00      ( k2_enumset1(k1_funct_1(o_0_0_xboole_0,sK1),k1_funct_1(o_0_0_xboole_0,sK1),k1_funct_1(o_0_0_xboole_0,sK1),k1_funct_1(o_0_0_xboole_0,sK1)) != k2_relat_1(o_0_0_xboole_0) ),
% 3.73/1.00      inference(demodulation,[status(thm)],[c_6925,c_3261]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_6953,plain,
% 3.73/1.00      ( k2_enumset1(k1_funct_1(o_0_0_xboole_0,sK1),k1_funct_1(o_0_0_xboole_0,sK1),k1_funct_1(o_0_0_xboole_0,sK1),k1_funct_1(o_0_0_xboole_0,sK1)) != o_0_0_xboole_0 ),
% 3.73/1.00      inference(light_normalisation,[status(thm)],[c_6950,c_17]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_6979,plain,
% 3.73/1.00      ( o_0_0_xboole_0 != o_0_0_xboole_0 ),
% 3.73/1.00      inference(demodulation,[status(thm)],[c_6978,c_6953]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_6980,plain,
% 3.73/1.00      ( $false ),
% 3.73/1.00      inference(equality_resolution_simp,[status(thm)],[c_6979]) ).
% 3.73/1.00  
% 3.73/1.00  
% 3.73/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.73/1.00  
% 3.73/1.00  ------                               Statistics
% 3.73/1.00  
% 3.73/1.00  ------ General
% 3.73/1.00  
% 3.73/1.00  abstr_ref_over_cycles:                  0
% 3.73/1.00  abstr_ref_under_cycles:                 0
% 3.73/1.00  gc_basic_clause_elim:                   0
% 3.73/1.00  forced_gc_time:                         0
% 3.73/1.00  parsing_time:                           0.017
% 3.73/1.00  unif_index_cands_time:                  0.
% 3.73/1.00  unif_index_add_time:                    0.
% 3.73/1.00  orderings_time:                         0.
% 3.73/1.00  out_proof_time:                         0.013
% 3.73/1.00  total_time:                             0.236
% 3.73/1.00  num_of_symbols:                         51
% 3.73/1.00  num_of_terms:                           6468
% 3.73/1.00  
% 3.73/1.00  ------ Preprocessing
% 3.73/1.00  
% 3.73/1.00  num_of_splits:                          0
% 3.73/1.00  num_of_split_atoms:                     0
% 3.73/1.00  num_of_reused_defs:                     0
% 3.73/1.00  num_eq_ax_congr_red:                    14
% 3.73/1.00  num_of_sem_filtered_clauses:            1
% 3.73/1.00  num_of_subtypes:                        0
% 3.73/1.00  monotx_restored_types:                  0
% 3.73/1.00  sat_num_of_epr_types:                   0
% 3.73/1.00  sat_num_of_non_cyclic_types:            0
% 3.73/1.00  sat_guarded_non_collapsed_types:        0
% 3.73/1.00  num_pure_diseq_elim:                    0
% 3.73/1.00  simp_replaced_by:                       0
% 3.73/1.00  res_preprocessed:                       164
% 3.73/1.00  prep_upred:                             0
% 3.73/1.00  prep_unflattend:                        15
% 3.73/1.00  smt_new_axioms:                         0
% 3.73/1.00  pred_elim_cands:                        4
% 3.73/1.00  pred_elim:                              2
% 3.73/1.00  pred_elim_cl:                           3
% 3.73/1.00  pred_elim_cycles:                       6
% 3.73/1.00  merged_defs:                            8
% 3.73/1.00  merged_defs_ncl:                        0
% 3.73/1.00  bin_hyper_res:                          8
% 3.73/1.00  prep_cycles:                            4
% 3.73/1.00  pred_elim_time:                         0.006
% 3.73/1.00  splitting_time:                         0.
% 3.73/1.00  sem_filter_time:                        0.
% 3.73/1.00  monotx_time:                            0.001
% 3.73/1.00  subtype_inf_time:                       0.
% 3.73/1.00  
% 3.73/1.00  ------ Problem properties
% 3.73/1.00  
% 3.73/1.00  clauses:                                33
% 3.73/1.00  conjectures:                            4
% 3.73/1.00  epr:                                    4
% 3.73/1.00  horn:                                   32
% 3.73/1.00  ground:                                 8
% 3.73/1.00  unary:                                  20
% 3.73/1.00  binary:                                 7
% 3.73/1.00  lits:                                   59
% 3.73/1.00  lits_eq:                                25
% 3.73/1.00  fd_pure:                                0
% 3.73/1.00  fd_pseudo:                              0
% 3.73/1.00  fd_cond:                                2
% 3.73/1.00  fd_pseudo_cond:                         2
% 3.73/1.00  ac_symbols:                             0
% 3.73/1.00  
% 3.73/1.00  ------ Propositional Solver
% 3.73/1.00  
% 3.73/1.00  prop_solver_calls:                      31
% 3.73/1.00  prop_fast_solver_calls:                 928
% 3.73/1.00  smt_solver_calls:                       0
% 3.73/1.00  smt_fast_solver_calls:                  0
% 3.73/1.00  prop_num_of_clauses:                    2972
% 3.73/1.00  prop_preprocess_simplified:             7128
% 3.73/1.00  prop_fo_subsumed:                       19
% 3.73/1.00  prop_solver_time:                       0.
% 3.73/1.00  smt_solver_time:                        0.
% 3.73/1.00  smt_fast_solver_time:                   0.
% 3.73/1.00  prop_fast_solver_time:                  0.
% 3.73/1.00  prop_unsat_core_time:                   0.
% 3.73/1.00  
% 3.73/1.00  ------ QBF
% 3.73/1.00  
% 3.73/1.00  qbf_q_res:                              0
% 3.73/1.00  qbf_num_tautologies:                    0
% 3.73/1.00  qbf_prep_cycles:                        0
% 3.73/1.00  
% 3.73/1.00  ------ BMC1
% 3.73/1.00  
% 3.73/1.00  bmc1_current_bound:                     -1
% 3.73/1.00  bmc1_last_solved_bound:                 -1
% 3.73/1.00  bmc1_unsat_core_size:                   -1
% 3.73/1.00  bmc1_unsat_core_parents_size:           -1
% 3.73/1.00  bmc1_merge_next_fun:                    0
% 3.73/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.73/1.00  
% 3.73/1.00  ------ Instantiation
% 3.73/1.00  
% 3.73/1.00  inst_num_of_clauses:                    809
% 3.73/1.00  inst_num_in_passive:                    151
% 3.73/1.00  inst_num_in_active:                     428
% 3.73/1.00  inst_num_in_unprocessed:                230
% 3.73/1.00  inst_num_of_loops:                      480
% 3.73/1.00  inst_num_of_learning_restarts:          0
% 3.73/1.00  inst_num_moves_active_passive:          48
% 3.73/1.00  inst_lit_activity:                      0
% 3.73/1.00  inst_lit_activity_moves:                0
% 3.73/1.00  inst_num_tautologies:                   0
% 3.73/1.00  inst_num_prop_implied:                  0
% 3.73/1.00  inst_num_existing_simplified:           0
% 3.73/1.00  inst_num_eq_res_simplified:             0
% 3.73/1.00  inst_num_child_elim:                    0
% 3.73/1.00  inst_num_of_dismatching_blockings:      327
% 3.73/1.00  inst_num_of_non_proper_insts:           1125
% 3.73/1.00  inst_num_of_duplicates:                 0
% 3.73/1.00  inst_inst_num_from_inst_to_res:         0
% 3.73/1.00  inst_dismatching_checking_time:         0.
% 3.73/1.00  
% 3.73/1.00  ------ Resolution
% 3.73/1.00  
% 3.73/1.00  res_num_of_clauses:                     0
% 3.73/1.00  res_num_in_passive:                     0
% 3.73/1.00  res_num_in_active:                      0
% 3.73/1.00  res_num_of_loops:                       168
% 3.73/1.00  res_forward_subset_subsumed:            138
% 3.73/1.00  res_backward_subset_subsumed:           2
% 3.73/1.00  res_forward_subsumed:                   0
% 3.73/1.00  res_backward_subsumed:                  0
% 3.73/1.00  res_forward_subsumption_resolution:     0
% 3.73/1.00  res_backward_subsumption_resolution:    0
% 3.73/1.00  res_clause_to_clause_subsumption:       560
% 3.73/1.00  res_orphan_elimination:                 0
% 3.73/1.00  res_tautology_del:                      65
% 3.73/1.00  res_num_eq_res_simplified:              0
% 3.73/1.00  res_num_sel_changes:                    0
% 3.73/1.00  res_moves_from_active_to_pass:          0
% 3.73/1.00  
% 3.73/1.00  ------ Superposition
% 3.73/1.00  
% 3.73/1.00  sup_time_total:                         0.
% 3.73/1.00  sup_time_generating:                    0.
% 3.73/1.00  sup_time_sim_full:                      0.
% 3.73/1.00  sup_time_sim_immed:                     0.
% 3.73/1.00  
% 3.73/1.00  sup_num_of_clauses:                     149
% 3.73/1.00  sup_num_in_active:                      52
% 3.73/1.00  sup_num_in_passive:                     97
% 3.73/1.00  sup_num_of_loops:                       95
% 3.73/1.00  sup_fw_superposition:                   105
% 3.73/1.00  sup_bw_superposition:                   169
% 3.73/1.00  sup_immediate_simplified:               45
% 3.73/1.00  sup_given_eliminated:                   1
% 3.73/1.00  comparisons_done:                       0
% 3.73/1.00  comparisons_avoided:                    0
% 3.73/1.00  
% 3.73/1.00  ------ Simplifications
% 3.73/1.00  
% 3.73/1.00  
% 3.73/1.00  sim_fw_subset_subsumed:                 13
% 3.73/1.00  sim_bw_subset_subsumed:                 13
% 3.73/1.00  sim_fw_subsumed:                        25
% 3.73/1.00  sim_bw_subsumed:                        1
% 3.73/1.00  sim_fw_subsumption_res:                 0
% 3.73/1.00  sim_bw_subsumption_res:                 0
% 3.73/1.00  sim_tautology_del:                      4
% 3.73/1.00  sim_eq_tautology_del:                   20
% 3.73/1.00  sim_eq_res_simp:                        0
% 3.73/1.00  sim_fw_demodulated:                     26
% 3.73/1.00  sim_bw_demodulated:                     44
% 3.73/1.00  sim_light_normalised:                   14
% 3.73/1.00  sim_joinable_taut:                      0
% 3.73/1.00  sim_joinable_simp:                      0
% 3.73/1.00  sim_ac_normalised:                      0
% 3.73/1.00  sim_smt_subsumption:                    0
% 3.73/1.00  
%------------------------------------------------------------------------------
