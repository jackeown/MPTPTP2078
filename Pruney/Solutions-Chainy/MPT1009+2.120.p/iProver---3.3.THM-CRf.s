%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:52 EST 2020

% Result     : Theorem 3.44s
% Output     : CNFRefutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :  145 (1649 expanded)
%              Number of clauses        :   71 ( 404 expanded)
%              Number of leaves         :   20 ( 385 expanded)
%              Depth                    :   30
%              Number of atoms          :  378 (3921 expanded)
%              Number of equality atoms :  158 (1525 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
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
    inference(nnf_transformation,[],[f8])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f20,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f22,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f38,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f39,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f38])).

fof(f50,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
        & k1_xboole_0 != X1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1)))
      & k1_xboole_0 != sK2
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1)))
    & k1_xboole_0 != sK2
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f39,f50])).

fof(f83,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) ),
    inference(cnf_transformation,[],[f51])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f86,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f56,f57])).

fof(f87,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f55,f86])).

fof(f93,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
    inference(definition_unfolding,[],[f83,f87])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f42])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f58,f87,f87])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f12,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f91,plain,(
    ! [X0,X1] :
      ( k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f73,f87,f87])).

fof(f82,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f85,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1))) ),
    inference(cnf_transformation,[],[f51])).

fof(f92,plain,(
    ~ r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) ),
    inference(definition_unfolding,[],[f85,f87,f87])).

fof(f15,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( ! [X3] :
              ( r2_hidden(X3,X0)
             => r2_hidden(k1_funct_1(X2,X3),X1) )
          & k1_relat_1(X2) = X0 )
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( ! [X3] :
              ( r2_hidden(X3,X0)
             => r2_hidden(k1_funct_1(X2,X3),X1) )
          & k1_relat_1(X2) = X0 )
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) ) ) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1)
        & r2_hidden(sK0(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
      | ( ~ r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1)
        & r2_hidden(sK0(X0,X1,X2),X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f48])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_hidden(sK0(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f101,plain,(
    ! [X2,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | r2_hidden(sK0(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f80])).

fof(f6,axiom,(
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
    inference(nnf_transformation,[],[f6])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f44])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f99,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f62])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_9,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1220,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1218,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2371,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1220,c_1218])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1212,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_20,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_15,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_346,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_20,c_15])).

cnf(c_1210,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_346])).

cnf(c_1642,plain,
    ( r1_tarski(k1_relat_1(sK4),k2_enumset1(sK1,sK1,sK1,sK1)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1212,c_1210])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1221,plain,
    ( k2_enumset1(X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4521,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK4)
    | k1_relat_1(sK4) = k1_xboole_0
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1642,c_1221])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_10,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_213,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_214,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_213])).

cnf(c_259,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_13,c_214])).

cnf(c_1794,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
    inference(resolution,[status(thm)],[c_11,c_29])).

cnf(c_2087,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))
    | v1_relat_1(sK4) ),
    inference(resolution,[status(thm)],[c_259,c_1794])).

cnf(c_16,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2092,plain,
    ( v1_relat_1(sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2087,c_16])).

cnf(c_4568,plain,
    ( ~ v1_relat_1(sK4)
    | k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK4)
    | k1_relat_1(sK4) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4521])).

cnf(c_5016,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4521,c_2092,c_4568])).

cnf(c_5017,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK4)
    | k1_relat_1(sK4) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_5016])).

cnf(c_18,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_395,plain,
    ( ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_30])).

cnf(c_396,plain,
    ( ~ v1_relat_1(sK4)
    | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK4)
    | k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k2_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_395])).

cnf(c_1209,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK4)
    | k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k2_relat_1(sK4)
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_396])).

cnf(c_5022,plain,
    ( k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) = k2_relat_1(sK4)
    | k1_relat_1(sK4) = k1_xboole_0
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5017,c_1209])).

cnf(c_5073,plain,
    ( ~ v1_relat_1(sK4)
    | k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) = k2_relat_1(sK4)
    | k1_relat_1(sK4) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5022])).

cnf(c_5427,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) = k2_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5022,c_2093])).

cnf(c_5428,plain,
    ( k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) = k2_relat_1(sK4)
    | k1_relat_1(sK4) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_5427])).

cnf(c_5433,plain,
    ( k2_enumset1(k1_funct_1(sK4,k1_funct_1(sK4,sK1)),k1_funct_1(sK4,k1_funct_1(sK4,sK1)),k1_funct_1(sK4,k1_funct_1(sK4,sK1)),k1_funct_1(sK4,k1_funct_1(sK4,sK1))) = k2_relat_1(sK4)
    | k2_relat_1(sK4) != k1_relat_1(sK4)
    | k1_relat_1(sK4) = k1_xboole_0
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5428,c_1209])).

cnf(c_2093,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2092])).

cnf(c_17,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1216,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1214,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3502,plain,
    ( k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,X0) = k9_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_1212,c_1214])).

cnf(c_27,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1213,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3795,plain,
    ( r1_tarski(k9_relat_1(sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3502,c_1213])).

cnf(c_5434,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | r1_tarski(k9_relat_1(sK4,sK3),k2_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5428,c_3795])).

cnf(c_5579,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1216,c_5434])).

cnf(c_5582,plain,
    ( k1_relat_1(sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5433,c_2093,c_5579])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_24,plain,
    ( r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_365,plain,
    ( r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_30])).

cnf(c_366,plain,
    ( r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_365])).

cnf(c_422,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(sK4)
    | sK0(k1_relat_1(sK4),X0,sK4) != X2
    | k1_relat_1(sK4) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_366])).

cnf(c_423,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
    | ~ r1_tarski(k1_relat_1(sK4),sK0(k1_relat_1(sK4),X0,sK4))
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_422])).

cnf(c_1208,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
    | r1_tarski(k1_relat_1(sK4),sK0(k1_relat_1(sK4),X0,sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_423])).

cnf(c_5602,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) = iProver_top
    | r1_tarski(k1_xboole_0,sK0(k1_xboole_0,X0,sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5582,c_1208])).

cnf(c_7,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_5613,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,sK0(k1_xboole_0,X0,sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5602,c_7])).

cnf(c_6384,plain,
    ( r1_tarski(k1_xboole_0,sK0(k1_xboole_0,X0,sK4)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5613,c_2093])).

cnf(c_6385,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,sK0(k1_xboole_0,X0,sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6384])).

cnf(c_7701,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2371,c_6385])).

cnf(c_3507,plain,
    ( k7_relset_1(k1_xboole_0,X0,X1,X2) = k9_relat_1(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_1214])).

cnf(c_9203,plain,
    ( k7_relset_1(k1_xboole_0,X0,sK4,X1) = k9_relat_1(sK4,X1) ),
    inference(superposition,[status(thm)],[c_7701,c_3507])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1215,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3270,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k7_relset_1(X1,X2,X0,X3),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1215,c_1218])).

cnf(c_11921,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
    | r1_tarski(k9_relat_1(sK4,X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_9203,c_3270])).

cnf(c_11943,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k9_relat_1(sK4,X0),X1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11921,c_7])).

cnf(c_12809,plain,
    ( r1_tarski(k9_relat_1(sK4,X0),X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11943,c_7701])).

cnf(c_12820,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_12809,c_3795])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:40:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.44/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.44/1.00  
% 3.44/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.44/1.00  
% 3.44/1.00  ------  iProver source info
% 3.44/1.00  
% 3.44/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.44/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.44/1.00  git: non_committed_changes: false
% 3.44/1.00  git: last_make_outside_of_git: false
% 3.44/1.00  
% 3.44/1.00  ------ 
% 3.44/1.00  ------ Parsing...
% 3.44/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.44/1.00  
% 3.44/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.44/1.00  
% 3.44/1.00  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.44/1.00  
% 3.44/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.44/1.00  ------ Proving...
% 3.44/1.00  ------ Problem Properties 
% 3.44/1.00  
% 3.44/1.00  
% 3.44/1.00  clauses                                 25
% 3.44/1.00  conjectures                             3
% 3.44/1.00  EPR                                     4
% 3.44/1.00  Horn                                    21
% 3.44/1.00  unary                                   10
% 3.44/1.00  binary                                  5
% 3.44/1.00  lits                                    51
% 3.44/1.00  lits eq                                 13
% 3.44/1.00  fd_pure                                 0
% 3.44/1.00  fd_pseudo                               0
% 3.44/1.00  fd_cond                                 1
% 3.44/1.00  fd_pseudo_cond                          2
% 3.44/1.00  AC symbols                              0
% 3.44/1.00  
% 3.44/1.00  ------ Input Options Time Limit: Unbounded
% 3.44/1.00  
% 3.44/1.00  
% 3.44/1.00  ------ 
% 3.44/1.00  Current options:
% 3.44/1.00  ------ 
% 3.44/1.00  
% 3.44/1.00  
% 3.44/1.00  
% 3.44/1.00  
% 3.44/1.00  ------ Proving...
% 3.44/1.00  
% 3.44/1.00  
% 3.44/1.00  % SZS status Theorem for theBenchmark.p
% 3.44/1.00  
% 3.44/1.00   Resolution empty clause
% 3.44/1.00  
% 3.44/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.44/1.00  
% 3.44/1.00  fof(f7,axiom,(
% 3.44/1.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.44/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/1.00  
% 3.44/1.00  fof(f64,plain,(
% 3.44/1.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.44/1.00    inference(cnf_transformation,[],[f7])).
% 3.44/1.00  
% 3.44/1.00  fof(f8,axiom,(
% 3.44/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.44/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/1.00  
% 3.44/1.00  fof(f46,plain,(
% 3.44/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.44/1.00    inference(nnf_transformation,[],[f8])).
% 3.44/1.00  
% 3.44/1.00  fof(f65,plain,(
% 3.44/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.44/1.00    inference(cnf_transformation,[],[f46])).
% 3.44/1.00  
% 3.44/1.00  fof(f20,conjecture,(
% 3.44/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 3.44/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/1.00  
% 3.44/1.00  fof(f21,negated_conjecture,(
% 3.44/1.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 3.44/1.00    inference(negated_conjecture,[],[f20])).
% 3.44/1.00  
% 3.44/1.00  fof(f22,plain,(
% 3.44/1.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 3.44/1.00    inference(pure_predicate_removal,[],[f21])).
% 3.44/1.00  
% 3.44/1.00  fof(f38,plain,(
% 3.44/1.00    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 3.44/1.00    inference(ennf_transformation,[],[f22])).
% 3.44/1.00  
% 3.44/1.00  fof(f39,plain,(
% 3.44/1.00    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 3.44/1.00    inference(flattening,[],[f38])).
% 3.44/1.00  
% 3.44/1.00  fof(f50,plain,(
% 3.44/1.00    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1))) & k1_xboole_0 != sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_1(sK4))),
% 3.44/1.00    introduced(choice_axiom,[])).
% 3.44/1.00  
% 3.44/1.00  fof(f51,plain,(
% 3.44/1.00    ~r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1))) & k1_xboole_0 != sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_1(sK4)),
% 3.44/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f39,f50])).
% 3.44/1.00  
% 3.44/1.00  fof(f83,plain,(
% 3.44/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))),
% 3.44/1.00    inference(cnf_transformation,[],[f51])).
% 3.44/1.00  
% 3.44/1.00  fof(f2,axiom,(
% 3.44/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.44/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/1.00  
% 3.44/1.00  fof(f55,plain,(
% 3.44/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.44/1.00    inference(cnf_transformation,[],[f2])).
% 3.44/1.00  
% 3.44/1.00  fof(f3,axiom,(
% 3.44/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.44/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/1.00  
% 3.44/1.00  fof(f56,plain,(
% 3.44/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.44/1.00    inference(cnf_transformation,[],[f3])).
% 3.44/1.00  
% 3.44/1.00  fof(f4,axiom,(
% 3.44/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.44/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/1.00  
% 3.44/1.00  fof(f57,plain,(
% 3.44/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.44/1.00    inference(cnf_transformation,[],[f4])).
% 3.44/1.00  
% 3.44/1.00  fof(f86,plain,(
% 3.44/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.44/1.00    inference(definition_unfolding,[],[f56,f57])).
% 3.44/1.00  
% 3.44/1.00  fof(f87,plain,(
% 3.44/1.00    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.44/1.00    inference(definition_unfolding,[],[f55,f86])).
% 3.44/1.00  
% 3.44/1.00  fof(f93,plain,(
% 3.44/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))),
% 3.44/1.00    inference(definition_unfolding,[],[f83,f87])).
% 3.44/1.00  
% 3.44/1.00  fof(f16,axiom,(
% 3.44/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.44/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/1.00  
% 3.44/1.00  fof(f24,plain,(
% 3.44/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.44/1.00    inference(pure_predicate_removal,[],[f16])).
% 3.44/1.00  
% 3.44/1.00  fof(f33,plain,(
% 3.44/1.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.44/1.00    inference(ennf_transformation,[],[f24])).
% 3.44/1.00  
% 3.44/1.00  fof(f75,plain,(
% 3.44/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.44/1.00    inference(cnf_transformation,[],[f33])).
% 3.44/1.00  
% 3.44/1.00  fof(f11,axiom,(
% 3.44/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.44/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/1.00  
% 3.44/1.00  fof(f28,plain,(
% 3.44/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.44/1.00    inference(ennf_transformation,[],[f11])).
% 3.44/1.00  
% 3.44/1.00  fof(f47,plain,(
% 3.44/1.00    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.44/1.00    inference(nnf_transformation,[],[f28])).
% 3.44/1.00  
% 3.44/1.00  fof(f69,plain,(
% 3.44/1.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.44/1.00    inference(cnf_transformation,[],[f47])).
% 3.44/1.00  
% 3.44/1.00  fof(f5,axiom,(
% 3.44/1.00    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 3.44/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/1.00  
% 3.44/1.00  fof(f42,plain,(
% 3.44/1.00    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 3.44/1.00    inference(nnf_transformation,[],[f5])).
% 3.44/1.00  
% 3.44/1.00  fof(f43,plain,(
% 3.44/1.00    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 3.44/1.00    inference(flattening,[],[f42])).
% 3.44/1.00  
% 3.44/1.00  fof(f58,plain,(
% 3.44/1.00    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 3.44/1.00    inference(cnf_transformation,[],[f43])).
% 3.44/1.00  
% 3.44/1.00  fof(f90,plain,(
% 3.44/1.00    ( ! [X0,X1] : (k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))) )),
% 3.44/1.00    inference(definition_unfolding,[],[f58,f87,f87])).
% 3.44/1.00  
% 3.44/1.00  fof(f10,axiom,(
% 3.44/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.44/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/1.00  
% 3.44/1.00  fof(f27,plain,(
% 3.44/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.44/1.00    inference(ennf_transformation,[],[f10])).
% 3.44/1.00  
% 3.44/1.00  fof(f68,plain,(
% 3.44/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.44/1.00    inference(cnf_transformation,[],[f27])).
% 3.44/1.00  
% 3.44/1.00  fof(f66,plain,(
% 3.44/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.44/1.00    inference(cnf_transformation,[],[f46])).
% 3.44/1.00  
% 3.44/1.00  fof(f12,axiom,(
% 3.44/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.44/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/1.00  
% 3.44/1.00  fof(f71,plain,(
% 3.44/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.44/1.00    inference(cnf_transformation,[],[f12])).
% 3.44/1.00  
% 3.44/1.00  fof(f14,axiom,(
% 3.44/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 3.44/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/1.00  
% 3.44/1.00  fof(f30,plain,(
% 3.44/1.00    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.44/1.00    inference(ennf_transformation,[],[f14])).
% 3.44/1.00  
% 3.44/1.00  fof(f31,plain,(
% 3.44/1.00    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.44/1.00    inference(flattening,[],[f30])).
% 3.44/1.00  
% 3.44/1.00  fof(f73,plain,(
% 3.44/1.00    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.44/1.00    inference(cnf_transformation,[],[f31])).
% 3.44/1.00  
% 3.44/1.00  fof(f91,plain,(
% 3.44/1.00    ( ! [X0,X1] : (k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1) | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.44/1.00    inference(definition_unfolding,[],[f73,f87,f87])).
% 3.44/1.00  
% 3.44/1.00  fof(f82,plain,(
% 3.44/1.00    v1_funct_1(sK4)),
% 3.44/1.00    inference(cnf_transformation,[],[f51])).
% 3.44/1.00  
% 3.44/1.00  fof(f13,axiom,(
% 3.44/1.00    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 3.44/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/1.00  
% 3.44/1.00  fof(f29,plain,(
% 3.44/1.00    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.44/1.00    inference(ennf_transformation,[],[f13])).
% 3.44/1.00  
% 3.44/1.00  fof(f72,plain,(
% 3.44/1.00    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.44/1.00    inference(cnf_transformation,[],[f29])).
% 3.44/1.00  
% 3.44/1.00  fof(f18,axiom,(
% 3.44/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.44/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/1.00  
% 3.44/1.00  fof(f35,plain,(
% 3.44/1.00    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.44/1.00    inference(ennf_transformation,[],[f18])).
% 3.44/1.00  
% 3.44/1.00  fof(f77,plain,(
% 3.44/1.00    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.44/1.00    inference(cnf_transformation,[],[f35])).
% 3.44/1.00  
% 3.44/1.00  fof(f85,plain,(
% 3.44/1.00    ~r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1)))),
% 3.44/1.00    inference(cnf_transformation,[],[f51])).
% 3.44/1.00  
% 3.44/1.00  fof(f92,plain,(
% 3.44/1.00    ~r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)))),
% 3.44/1.00    inference(definition_unfolding,[],[f85,f87,f87])).
% 3.44/1.00  
% 3.44/1.00  fof(f15,axiom,(
% 3.44/1.00    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.44/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/1.00  
% 3.44/1.00  fof(f32,plain,(
% 3.44/1.00    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.44/1.00    inference(ennf_transformation,[],[f15])).
% 3.44/1.00  
% 3.44/1.00  fof(f74,plain,(
% 3.44/1.00    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.44/1.00    inference(cnf_transformation,[],[f32])).
% 3.44/1.00  
% 3.44/1.00  fof(f19,axiom,(
% 3.44/1.00    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 3.44/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/1.00  
% 3.44/1.00  fof(f23,plain,(
% 3.44/1.00    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))))),
% 3.44/1.00    inference(pure_predicate_removal,[],[f19])).
% 3.44/1.00  
% 3.44/1.00  fof(f36,plain,(
% 3.44/1.00    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.44/1.00    inference(ennf_transformation,[],[f23])).
% 3.44/1.00  
% 3.44/1.00  fof(f37,plain,(
% 3.44/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.44/1.00    inference(flattening,[],[f36])).
% 3.44/1.00  
% 3.44/1.00  fof(f48,plain,(
% 3.44/1.00    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) => (~r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1) & r2_hidden(sK0(X0,X1,X2),X0)))),
% 3.44/1.00    introduced(choice_axiom,[])).
% 3.44/1.00  
% 3.44/1.00  fof(f49,plain,(
% 3.44/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) | (~r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.44/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f48])).
% 3.44/1.00  
% 3.44/1.00  fof(f80,plain,(
% 3.44/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_hidden(sK0(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.44/1.00    inference(cnf_transformation,[],[f49])).
% 3.44/1.00  
% 3.44/1.00  fof(f101,plain,(
% 3.44/1.00    ( ! [X2,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | r2_hidden(sK0(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.44/1.00    inference(equality_resolution,[],[f80])).
% 3.44/1.00  
% 3.44/1.00  fof(f6,axiom,(
% 3.44/1.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.44/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/1.00  
% 3.44/1.00  fof(f44,plain,(
% 3.44/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.44/1.00    inference(nnf_transformation,[],[f6])).
% 3.44/1.00  
% 3.44/1.00  fof(f45,plain,(
% 3.44/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.44/1.00    inference(flattening,[],[f44])).
% 3.44/1.00  
% 3.44/1.00  fof(f62,plain,(
% 3.44/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.44/1.00    inference(cnf_transformation,[],[f45])).
% 3.44/1.00  
% 3.44/1.00  fof(f99,plain,(
% 3.44/1.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.44/1.00    inference(equality_resolution,[],[f62])).
% 3.44/1.00  
% 3.44/1.00  fof(f17,axiom,(
% 3.44/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 3.44/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/1.00  
% 3.44/1.00  fof(f34,plain,(
% 3.44/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.44/1.00    inference(ennf_transformation,[],[f17])).
% 3.44/1.00  
% 3.44/1.00  fof(f76,plain,(
% 3.44/1.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.44/1.00    inference(cnf_transformation,[],[f34])).
% 3.44/1.00  
% 3.44/1.00  cnf(c_9,plain,
% 3.44/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.44/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_1220,plain,
% 3.44/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.44/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_11,plain,
% 3.44/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.44/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_1218,plain,
% 3.44/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.44/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.44/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_2371,plain,
% 3.44/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.44/1.00      inference(superposition,[status(thm)],[c_1220,c_1218]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_29,negated_conjecture,
% 3.44/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
% 3.44/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_1212,plain,
% 3.44/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) = iProver_top ),
% 3.44/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_20,plain,
% 3.44/1.00      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.44/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_15,plain,
% 3.44/1.00      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 3.44/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_346,plain,
% 3.44/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.44/1.00      | r1_tarski(k1_relat_1(X0),X1)
% 3.44/1.00      | ~ v1_relat_1(X0) ),
% 3.44/1.00      inference(resolution,[status(thm)],[c_20,c_15]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_1210,plain,
% 3.44/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.44/1.00      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 3.44/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.44/1.00      inference(predicate_to_equality,[status(thm)],[c_346]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_1642,plain,
% 3.44/1.00      ( r1_tarski(k1_relat_1(sK4),k2_enumset1(sK1,sK1,sK1,sK1)) = iProver_top
% 3.44/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.44/1.00      inference(superposition,[status(thm)],[c_1212,c_1210]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_5,plain,
% 3.44/1.00      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
% 3.44/1.00      | k2_enumset1(X1,X1,X1,X1) = X0
% 3.44/1.00      | k1_xboole_0 = X0 ),
% 3.44/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_1221,plain,
% 3.44/1.00      ( k2_enumset1(X0,X0,X0,X0) = X1
% 3.44/1.00      | k1_xboole_0 = X1
% 3.44/1.00      | r1_tarski(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
% 3.44/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_4521,plain,
% 3.44/1.00      ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK4)
% 3.44/1.00      | k1_relat_1(sK4) = k1_xboole_0
% 3.44/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.44/1.00      inference(superposition,[status(thm)],[c_1642,c_1221]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_13,plain,
% 3.44/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.44/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_10,plain,
% 3.44/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.44/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_213,plain,
% 3.44/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.44/1.00      inference(prop_impl,[status(thm)],[c_10]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_214,plain,
% 3.44/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.44/1.00      inference(renaming,[status(thm)],[c_213]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_259,plain,
% 3.44/1.00      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.44/1.00      inference(bin_hyper_res,[status(thm)],[c_13,c_214]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_1794,plain,
% 3.44/1.00      ( r1_tarski(sK4,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
% 3.44/1.00      inference(resolution,[status(thm)],[c_11,c_29]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_2087,plain,
% 3.44/1.00      ( ~ v1_relat_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))
% 3.44/1.00      | v1_relat_1(sK4) ),
% 3.44/1.00      inference(resolution,[status(thm)],[c_259,c_1794]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_16,plain,
% 3.44/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.44/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_2092,plain,
% 3.44/1.00      ( v1_relat_1(sK4) ),
% 3.44/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_2087,c_16]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_4568,plain,
% 3.44/1.00      ( ~ v1_relat_1(sK4)
% 3.44/1.00      | k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK4)
% 3.44/1.00      | k1_relat_1(sK4) = k1_xboole_0 ),
% 3.44/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_4521]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_5016,plain,
% 3.44/1.00      ( k1_relat_1(sK4) = k1_xboole_0
% 3.44/1.00      | k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK4) ),
% 3.44/1.00      inference(global_propositional_subsumption,
% 3.44/1.00                [status(thm)],
% 3.44/1.00                [c_4521,c_2092,c_4568]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_5017,plain,
% 3.44/1.00      ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK4)
% 3.44/1.00      | k1_relat_1(sK4) = k1_xboole_0 ),
% 3.44/1.00      inference(renaming,[status(thm)],[c_5016]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_18,plain,
% 3.44/1.00      ( ~ v1_funct_1(X0)
% 3.44/1.00      | ~ v1_relat_1(X0)
% 3.44/1.00      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 3.44/1.00      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
% 3.44/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_30,negated_conjecture,
% 3.44/1.00      ( v1_funct_1(sK4) ),
% 3.44/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_395,plain,
% 3.44/1.00      ( ~ v1_relat_1(X0)
% 3.44/1.00      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 3.44/1.00      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
% 3.44/1.00      | sK4 != X0 ),
% 3.44/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_30]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_396,plain,
% 3.44/1.00      ( ~ v1_relat_1(sK4)
% 3.44/1.00      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK4)
% 3.44/1.00      | k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k2_relat_1(sK4) ),
% 3.44/1.00      inference(unflattening,[status(thm)],[c_395]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_1209,plain,
% 3.44/1.00      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK4)
% 3.44/1.00      | k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k2_relat_1(sK4)
% 3.44/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.44/1.00      inference(predicate_to_equality,[status(thm)],[c_396]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_5022,plain,
% 3.44/1.00      ( k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) = k2_relat_1(sK4)
% 3.44/1.00      | k1_relat_1(sK4) = k1_xboole_0
% 3.44/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.44/1.00      inference(superposition,[status(thm)],[c_5017,c_1209]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_5073,plain,
% 3.44/1.00      ( ~ v1_relat_1(sK4)
% 3.44/1.00      | k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) = k2_relat_1(sK4)
% 3.44/1.00      | k1_relat_1(sK4) = k1_xboole_0 ),
% 3.44/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_5022]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_5427,plain,
% 3.44/1.00      ( k1_relat_1(sK4) = k1_xboole_0
% 3.44/1.00      | k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) = k2_relat_1(sK4) ),
% 3.44/1.00      inference(global_propositional_subsumption,[status(thm)],[c_5022,c_2093]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_5428,plain,
% 3.44/1.00      ( k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) = k2_relat_1(sK4)
% 3.44/1.00      | k1_relat_1(sK4) = k1_xboole_0 ),
% 3.44/1.00      inference(renaming,[status(thm)],[c_5427]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_5433,plain,
% 3.44/1.00      ( k2_enumset1(k1_funct_1(sK4,k1_funct_1(sK4,sK1)),k1_funct_1(sK4,k1_funct_1(sK4,sK1)),k1_funct_1(sK4,k1_funct_1(sK4,sK1)),k1_funct_1(sK4,k1_funct_1(sK4,sK1))) = k2_relat_1(sK4)
% 3.44/1.00      | k2_relat_1(sK4) != k1_relat_1(sK4)
% 3.44/1.00      | k1_relat_1(sK4) = k1_xboole_0
% 3.44/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.44/1.00      inference(superposition,[status(thm)],[c_5428,c_1209]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_2093,plain,
% 3.44/1.00      ( v1_relat_1(sK4) = iProver_top ),
% 3.44/1.00      inference(predicate_to_equality,[status(thm)],[c_2092]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_17,plain,
% 3.44/1.00      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 3.44/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_1216,plain,
% 3.44/1.00      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) = iProver_top
% 3.44/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.44/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_22,plain,
% 3.44/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.44/1.00      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.44/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_1214,plain,
% 3.44/1.00      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.44/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.44/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_3502,plain,
% 3.44/1.00      ( k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,X0) = k9_relat_1(sK4,X0) ),
% 3.44/1.00      inference(superposition,[status(thm)],[c_1212,c_1214]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_27,negated_conjecture,
% 3.44/1.00      ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) ),
% 3.44/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_1213,plain,
% 3.44/1.00      ( r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
% 3.44/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_3795,plain,
% 3.44/1.00      ( r1_tarski(k9_relat_1(sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
% 3.44/1.00      inference(demodulation,[status(thm)],[c_3502,c_1213]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_5434,plain,
% 3.44/1.00      ( k1_relat_1(sK4) = k1_xboole_0
% 3.44/1.00      | r1_tarski(k9_relat_1(sK4,sK3),k2_relat_1(sK4)) != iProver_top ),
% 3.44/1.00      inference(superposition,[status(thm)],[c_5428,c_3795]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_5579,plain,
% 3.44/1.00      ( k1_relat_1(sK4) = k1_xboole_0 | v1_relat_1(sK4) != iProver_top ),
% 3.44/1.00      inference(superposition,[status(thm)],[c_1216,c_5434]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_5582,plain,
% 3.44/1.00      ( k1_relat_1(sK4) = k1_xboole_0 ),
% 3.44/1.00      inference(global_propositional_subsumption,
% 3.44/1.00                [status(thm)],
% 3.44/1.00                [c_5433,c_2093,c_5579]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_19,plain,
% 3.44/1.00      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 3.44/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_24,plain,
% 3.44/1.00      ( r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 3.44/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.44/1.00      | ~ v1_funct_1(X0)
% 3.44/1.00      | ~ v1_relat_1(X0) ),
% 3.44/1.00      inference(cnf_transformation,[],[f101]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_365,plain,
% 3.44/1.00      ( r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 3.44/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.44/1.00      | ~ v1_relat_1(X0)
% 3.44/1.00      | sK4 != X0 ),
% 3.44/1.00      inference(resolution_lifted,[status(thm)],[c_24,c_30]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_366,plain,
% 3.44/1.00      ( r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4))
% 3.44/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
% 3.44/1.00      | ~ v1_relat_1(sK4) ),
% 3.44/1.00      inference(unflattening,[status(thm)],[c_365]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_422,plain,
% 3.44/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
% 3.44/1.00      | ~ r1_tarski(X1,X2)
% 3.44/1.00      | ~ v1_relat_1(sK4)
% 3.44/1.00      | sK0(k1_relat_1(sK4),X0,sK4) != X2
% 3.44/1.00      | k1_relat_1(sK4) != X1 ),
% 3.44/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_366]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_423,plain,
% 3.44/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
% 3.44/1.00      | ~ r1_tarski(k1_relat_1(sK4),sK0(k1_relat_1(sK4),X0,sK4))
% 3.44/1.00      | ~ v1_relat_1(sK4) ),
% 3.44/1.00      inference(unflattening,[status(thm)],[c_422]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_1208,plain,
% 3.44/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
% 3.44/1.00      | r1_tarski(k1_relat_1(sK4),sK0(k1_relat_1(sK4),X0,sK4)) != iProver_top
% 3.44/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.44/1.00      inference(predicate_to_equality,[status(thm)],[c_423]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_5602,plain,
% 3.44/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) = iProver_top
% 3.44/1.00      | r1_tarski(k1_xboole_0,sK0(k1_xboole_0,X0,sK4)) != iProver_top
% 3.44/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.44/1.00      inference(demodulation,[status(thm)],[c_5582,c_1208]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_7,plain,
% 3.44/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.44/1.00      inference(cnf_transformation,[],[f99]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_5613,plain,
% 3.44/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.44/1.00      | r1_tarski(k1_xboole_0,sK0(k1_xboole_0,X0,sK4)) != iProver_top
% 3.44/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.44/1.00      inference(light_normalisation,[status(thm)],[c_5602,c_7]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_6384,plain,
% 3.44/1.00      ( r1_tarski(k1_xboole_0,sK0(k1_xboole_0,X0,sK4)) != iProver_top
% 3.44/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.44/1.00      inference(global_propositional_subsumption,[status(thm)],[c_5613,c_2093]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_6385,plain,
% 3.44/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.44/1.00      | r1_tarski(k1_xboole_0,sK0(k1_xboole_0,X0,sK4)) != iProver_top ),
% 3.44/1.00      inference(renaming,[status(thm)],[c_6384]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_7701,plain,
% 3.44/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.44/1.00      inference(superposition,[status(thm)],[c_2371,c_6385]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_3507,plain,
% 3.44/1.00      ( k7_relset_1(k1_xboole_0,X0,X1,X2) = k9_relat_1(X1,X2)
% 3.44/1.00      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.44/1.00      inference(superposition,[status(thm)],[c_7,c_1214]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_9203,plain,
% 3.44/1.00      ( k7_relset_1(k1_xboole_0,X0,sK4,X1) = k9_relat_1(sK4,X1) ),
% 3.44/1.00      inference(superposition,[status(thm)],[c_7701,c_3507]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_21,plain,
% 3.44/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.44/1.00      | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
% 3.44/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_1215,plain,
% 3.44/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.44/1.00      | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) = iProver_top ),
% 3.44/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_3270,plain,
% 3.44/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.44/1.00      | r1_tarski(k7_relset_1(X1,X2,X0,X3),X2) = iProver_top ),
% 3.44/1.00      inference(superposition,[status(thm)],[c_1215,c_1218]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_11921,plain,
% 3.44/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
% 3.44/1.00      | r1_tarski(k9_relat_1(sK4,X1),X0) = iProver_top ),
% 3.44/1.00      inference(superposition,[status(thm)],[c_9203,c_3270]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_11943,plain,
% 3.44/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.44/1.00      | r1_tarski(k9_relat_1(sK4,X0),X1) = iProver_top ),
% 3.44/1.00      inference(light_normalisation,[status(thm)],[c_11921,c_7]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_12809,plain,
% 3.44/1.00      ( r1_tarski(k9_relat_1(sK4,X0),X1) = iProver_top ),
% 3.44/1.00      inference(global_propositional_subsumption,
% 3.44/1.00                [status(thm)],
% 3.44/1.00                [c_11943,c_7701]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_12820,plain,
% 3.44/1.00      ( $false ),
% 3.44/1.00      inference(superposition,[status(thm)],[c_12809,c_3795]) ).
% 3.44/1.00  
% 3.44/1.00  
% 3.44/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.44/1.00  
% 3.44/1.00  ------                               Statistics
% 3.44/1.00  
% 3.44/1.00  ------ Selected
% 3.44/1.00  
% 3.44/1.00  total_time:                             0.504
% 3.44/1.00  
%------------------------------------------------------------------------------
