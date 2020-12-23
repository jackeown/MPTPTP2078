%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:30 EST 2020

% Result     : Theorem 7.12s
% Output     : CNFRefutation 7.12s
% Verified   : 
% Statistics : Number of formulae       :  216 (13433 expanded)
%              Number of clauses        :  134 (3508 expanded)
%              Number of leaves         :   23 (3032 expanded)
%              Depth                    :   33
%              Number of atoms          :  511 (34647 expanded)
%              Number of equality atoms :  260 (13364 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f20,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f39,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f40,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f39])).

fof(f51,plain,
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

fof(f52,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1)))
    & k1_xboole_0 != sK2
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f40,f51])).

fof(f84,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) ),
    inference(cnf_transformation,[],[f52])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f87,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f57,f58])).

fof(f88,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f56,f87])).

fof(f94,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
    inference(definition_unfolding,[],[f84,f88])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f15])).

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

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f43])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f91,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f59,f88,f88])).

fof(f86,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1))) ),
    inference(cnf_transformation,[],[f52])).

fof(f93,plain,(
    ~ r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) ),
    inference(definition_unfolding,[],[f86,f88,f88])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f92,plain,(
    ! [X0,X1] :
      ( k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f72,f88,f88])).

fof(f83,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f52])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f41])).

fof(f55,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f96,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f23])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1)
        & r2_hidden(sK0(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
      | ( ~ r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1)
        & r2_hidden(sK0(X0,X1,X2),X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f49])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_hidden(sK0(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f102,plain,(
    ! [X2,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | r2_hidden(sK0(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f81])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f45])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f100,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f63])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f99,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f64])).

cnf(c_9,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1364,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1362,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2388,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1364,c_1362])).

cnf(c_15,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1361,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1355,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_19,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_14,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_347,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_19,c_14])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_351,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_347,c_18])).

cnf(c_352,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_351])).

cnf(c_1354,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_352])).

cnf(c_1854,plain,
    ( r1_tarski(k1_relat_1(sK4),k2_enumset1(sK1,sK1,sK1,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1355,c_1354])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1365,plain,
    ( k2_enumset1(X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3652,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK4)
    | k1_relat_1(sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1854,c_1365])).

cnf(c_27,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1422,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1509,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1422])).

cnf(c_16,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_398,plain,
    ( ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_30])).

cnf(c_399,plain,
    ( ~ v1_relat_1(sK4)
    | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK4)
    | k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k2_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_398])).

cnf(c_1353,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK4)
    | k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k2_relat_1(sK4)
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_399])).

cnf(c_1560,plain,
    ( k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k2_relat_1(sK4)
    | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1353,c_29,c_399,c_1509])).

cnf(c_1561,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK4)
    | k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k2_relat_1(sK4) ),
    inference(renaming,[status(thm)],[c_1560])).

cnf(c_1562,plain,
    ( k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) = k2_relat_1(sK4)
    | k2_enumset1(sK1,sK1,sK1,sK1) != k1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1561])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1592,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))
    | k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3) = k9_relat_1(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1857,plain,
    ( r1_tarski(k1_relat_1(sK4),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1854])).

cnf(c_856,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1400,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)))
    | k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3) != X0
    | k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) != X1 ),
    inference(instantiation,[status(thm)],[c_856])).

cnf(c_1471,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)))
    | ~ r1_tarski(k9_relat_1(sK4,sK3),X0)
    | k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3) != k9_relat_1(sK4,sK3)
    | k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) != X0 ),
    inference(instantiation,[status(thm)],[c_1400])).

cnf(c_1877,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)))
    | ~ r1_tarski(k9_relat_1(sK4,sK3),k2_relat_1(sK4))
    | k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3) != k9_relat_1(sK4,sK3)
    | k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) != k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1471])).

cnf(c_2362,plain,
    ( r1_tarski(k9_relat_1(sK4,sK3),k2_relat_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1830,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK4))
    | ~ r1_tarski(k1_relat_1(sK4),X0)
    | k1_relat_1(sK4) = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2443,plain,
    ( ~ r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4))
    | k1_relat_1(sK4) = k1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1830])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_2639,plain,
    ( r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1916,plain,
    ( ~ r1_tarski(k1_relat_1(X0),k2_enumset1(X1,X1,X1,X1))
    | k2_enumset1(X1,X1,X1,X1) = k1_relat_1(X0)
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3305,plain,
    ( ~ r1_tarski(k1_relat_1(sK4),k2_enumset1(sK1,sK1,sK1,sK1))
    | k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK4)
    | k1_xboole_0 = k1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1916])).

cnf(c_855,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1836,plain,
    ( X0 != X1
    | k1_relat_1(sK4) != X1
    | k1_relat_1(sK4) = X0 ),
    inference(instantiation,[status(thm)],[c_855])).

cnf(c_2460,plain,
    ( X0 != k1_relat_1(sK4)
    | k1_relat_1(sK4) = X0
    | k1_relat_1(sK4) != k1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1836])).

cnf(c_3593,plain,
    ( k1_relat_1(sK4) != k1_relat_1(sK4)
    | k1_relat_1(sK4) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2460])).

cnf(c_4002,plain,
    ( k1_relat_1(sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3652,c_29,c_27,c_1509,c_1562,c_1592,c_1857,c_1877,c_2362,c_2443,c_2639,c_3305,c_3593])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_24,plain,
    ( r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_368,plain,
    ( r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_30])).

cnf(c_369,plain,
    ( r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_368])).

cnf(c_425,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(sK4)
    | sK0(k1_relat_1(sK4),X0,sK4) != X2
    | k1_relat_1(sK4) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_369])).

cnf(c_426,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
    | ~ r1_tarski(k1_relat_1(sK4),sK0(k1_relat_1(sK4),X0,sK4))
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_425])).

cnf(c_1352,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
    | r1_tarski(k1_relat_1(sK4),sK0(k1_relat_1(sK4),X0,sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_426])).

cnf(c_32,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_427,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
    | r1_tarski(k1_relat_1(sK4),sK0(k1_relat_1(sK4),X0,sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_426])).

cnf(c_1510,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1509])).

cnf(c_1656,plain,
    ( r1_tarski(k1_relat_1(sK4),sK0(k1_relat_1(sK4),X0,sK4)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1352,c_32,c_427,c_1510])).

cnf(c_1657,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
    | r1_tarski(k1_relat_1(sK4),sK0(k1_relat_1(sK4),X0,sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1656])).

cnf(c_4022,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) = iProver_top
    | r1_tarski(k1_xboole_0,sK0(k1_xboole_0,X0,sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4002,c_1657])).

cnf(c_7,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_4024,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,sK0(k1_xboole_0,X0,sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4022,c_7])).

cnf(c_4500,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2388,c_4024])).

cnf(c_6598,plain,
    ( r1_tarski(sK4,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4500,c_1362])).

cnf(c_1369,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_8013,plain,
    ( sK4 = k1_xboole_0
    | r1_tarski(k1_xboole_0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6598,c_1369])).

cnf(c_2420,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4))
    | r1_tarski(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_3461,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4))
    | r1_tarski(k1_xboole_0,sK4) ),
    inference(instantiation,[status(thm)],[c_2420])).

cnf(c_3462,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) != iProver_top
    | r1_tarski(k1_xboole_0,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3461])).

cnf(c_3850,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_3851,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3850])).

cnf(c_8949,plain,
    ( sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8013,c_3462,c_3851])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1358,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3146,plain,
    ( k2_relset_1(k1_xboole_0,X0,X1) = k2_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_1358])).

cnf(c_6607,plain,
    ( k2_relset_1(k1_xboole_0,X0,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_4500,c_3146])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1359,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_8017,plain,
    ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(X0)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6607,c_1359])).

cnf(c_8024,plain,
    ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(X0)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8017,c_7])).

cnf(c_8312,plain,
    ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8024,c_4500])).

cnf(c_8956,plain,
    ( m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8949,c_8312])).

cnf(c_3781,plain,
    ( k2_relset_1(k1_xboole_0,X0,k2_relset_1(X1,k1_xboole_0,X2)) = k2_relat_1(k2_relset_1(X1,k1_xboole_0,X2))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1359,c_3146])).

cnf(c_6,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_3783,plain,
    ( k2_relset_1(k1_xboole_0,X0,k2_relset_1(X1,k1_xboole_0,X2)) = k2_relat_1(k2_relset_1(X1,k1_xboole_0,X2))
    | m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3781,c_6])).

cnf(c_6603,plain,
    ( k2_relset_1(k1_xboole_0,X0,k2_relset_1(X1,k1_xboole_0,sK4)) = k2_relat_1(k2_relset_1(X1,k1_xboole_0,sK4)) ),
    inference(superposition,[status(thm)],[c_4500,c_3783])).

cnf(c_3145,plain,
    ( k2_relset_1(X0,k1_xboole_0,X1) = k2_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_1358])).

cnf(c_6608,plain,
    ( k2_relset_1(X0,k1_xboole_0,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_4500,c_3145])).

cnf(c_6619,plain,
    ( k2_relset_1(k1_xboole_0,X0,k2_relat_1(sK4)) = k2_relat_1(k2_relat_1(sK4)) ),
    inference(demodulation,[status(thm)],[c_6603,c_6608])).

cnf(c_8862,plain,
    ( m1_subset_1(k2_relat_1(k2_relat_1(sK4)),k1_zfmisc_1(X0)) = iProver_top
    | m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6619,c_1359])).

cnf(c_8869,plain,
    ( m1_subset_1(k2_relat_1(k2_relat_1(sK4)),k1_zfmisc_1(X0)) = iProver_top
    | m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8862,c_7])).

cnf(c_9375,plain,
    ( m1_subset_1(k2_relat_1(k2_relat_1(k1_xboole_0)),k1_zfmisc_1(X0)) = iProver_top
    | m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8869,c_8949])).

cnf(c_2496,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relset_1(X1,X2,X0),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1359,c_1362])).

cnf(c_9382,plain,
    ( m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k2_relset_1(X0,X1,k2_relat_1(k2_relat_1(k1_xboole_0))),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_9375,c_2496])).

cnf(c_3139,plain,
    ( k2_relset_1(X0,X1,k2_relset_1(X2,k2_zfmisc_1(X0,X1),X3)) = k2_relat_1(k2_relset_1(X2,k2_zfmisc_1(X0,X1),X3))
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,k2_zfmisc_1(X0,X1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1359,c_1358])).

cnf(c_11876,plain,
    ( k2_relset_1(X0,X1,k2_relset_1(X2,k2_zfmisc_1(X0,X1),k2_relat_1(k1_xboole_0))) = k2_relat_1(k2_relset_1(X2,k2_zfmisc_1(X0,X1),k2_relat_1(k1_xboole_0))) ),
    inference(superposition,[status(thm)],[c_8956,c_3139])).

cnf(c_11471,plain,
    ( k2_relset_1(X0,X1,k2_relset_1(X2,k2_zfmisc_1(X0,X1),k1_xboole_0)) = k2_relat_1(k2_relset_1(X2,k2_zfmisc_1(X0,X1),k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_1364,c_3139])).

cnf(c_3137,plain,
    ( k2_relset_1(X0,X1,k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1364,c_1358])).

cnf(c_11480,plain,
    ( k2_relset_1(X0,X1,k2_relat_1(k1_xboole_0)) = k2_relat_1(k2_relat_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm)],[c_11471,c_3137])).

cnf(c_11941,plain,
    ( k2_relset_1(X0,X1,k2_relat_1(k2_relat_1(k1_xboole_0))) = k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0))) ),
    inference(demodulation,[status(thm)],[c_11876,c_11480])).

cnf(c_13899,plain,
    ( m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0))),X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9382,c_11941])).

cnf(c_13903,plain,
    ( k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0))) = X0
    | m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(X0,k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_13899,c_1369])).

cnf(c_3674,plain,
    ( k2_relset_1(X0,k1_xboole_0,k2_relset_1(X1,k1_xboole_0,X2)) = k2_relat_1(k2_relset_1(X1,k1_xboole_0,X2))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1359,c_3145])).

cnf(c_3676,plain,
    ( k2_relset_1(X0,k1_xboole_0,k2_relset_1(X1,k1_xboole_0,X2)) = k2_relat_1(k2_relset_1(X1,k1_xboole_0,X2))
    | m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3674,c_6])).

cnf(c_6604,plain,
    ( k2_relset_1(X0,k1_xboole_0,k2_relset_1(X1,k1_xboole_0,sK4)) = k2_relat_1(k2_relset_1(X1,k1_xboole_0,sK4)) ),
    inference(superposition,[status(thm)],[c_4500,c_3676])).

cnf(c_6615,plain,
    ( k2_relset_1(X0,k1_xboole_0,k2_relat_1(sK4)) = k2_relat_1(k2_relat_1(sK4)) ),
    inference(demodulation,[status(thm)],[c_6604,c_6608])).

cnf(c_8851,plain,
    ( m1_subset_1(k2_relat_1(k2_relat_1(sK4)),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6615,c_1359])).

cnf(c_8856,plain,
    ( m1_subset_1(k2_relat_1(k2_relat_1(sK4)),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8851,c_6])).

cnf(c_9292,plain,
    ( m1_subset_1(k2_relat_1(k2_relat_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8856,c_8949])).

cnf(c_9294,plain,
    ( m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k2_relat_1(k2_relat_1(k1_xboole_0)),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_9292,c_1362])).

cnf(c_13414,plain,
    ( r1_tarski(k2_relat_1(k2_relat_1(k1_xboole_0)),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_8956,c_9294])).

cnf(c_13417,plain,
    ( k2_relat_1(k2_relat_1(k1_xboole_0)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k2_relat_1(k2_relat_1(k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_13414,c_1369])).

cnf(c_15561,plain,
    ( k2_relat_1(k2_relat_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2388,c_13417])).

cnf(c_22707,plain,
    ( k2_relat_1(k1_xboole_0) = X0
    | m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(X0,k2_relat_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13903,c_15561])).

cnf(c_22712,plain,
    ( k2_relat_1(k1_xboole_0) = X0
    | r1_tarski(X0,k2_relat_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8956,c_22707])).

cnf(c_22719,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k2_relat_1(k1_xboole_0)
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1361,c_22712])).

cnf(c_22720,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2388,c_22712])).

cnf(c_22819,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_22719,c_22720])).

cnf(c_1602,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1603,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1602])).

cnf(c_2183,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2184,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2183])).

cnf(c_23099,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_22819,c_1603,c_2184])).

cnf(c_1357,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4506,plain,
    ( k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,X0) = k9_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_1355,c_1357])).

cnf(c_1356,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4636,plain,
    ( r1_tarski(k9_relat_1(sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4506,c_1356])).

cnf(c_8960,plain,
    ( r1_tarski(k9_relat_1(k1_xboole_0,sK3),k2_enumset1(k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8949,c_4636])).

cnf(c_23103,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_23099,c_8960])).

cnf(c_23666,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_2388,c_23103])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:56:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.12/1.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.12/1.48  
% 7.12/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.12/1.48  
% 7.12/1.48  ------  iProver source info
% 7.12/1.48  
% 7.12/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.12/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.12/1.48  git: non_committed_changes: false
% 7.12/1.48  git: last_make_outside_of_git: false
% 7.12/1.48  
% 7.12/1.48  ------ 
% 7.12/1.48  
% 7.12/1.48  ------ Input Options
% 7.12/1.48  
% 7.12/1.48  --out_options                           all
% 7.12/1.48  --tptp_safe_out                         true
% 7.12/1.48  --problem_path                          ""
% 7.12/1.48  --include_path                          ""
% 7.12/1.48  --clausifier                            res/vclausify_rel
% 7.12/1.48  --clausifier_options                    ""
% 7.12/1.48  --stdin                                 false
% 7.12/1.48  --stats_out                             all
% 7.12/1.48  
% 7.12/1.48  ------ General Options
% 7.12/1.48  
% 7.12/1.48  --fof                                   false
% 7.12/1.48  --time_out_real                         305.
% 7.12/1.48  --time_out_virtual                      -1.
% 7.12/1.48  --symbol_type_check                     false
% 7.12/1.48  --clausify_out                          false
% 7.12/1.48  --sig_cnt_out                           false
% 7.12/1.48  --trig_cnt_out                          false
% 7.12/1.48  --trig_cnt_out_tolerance                1.
% 7.12/1.48  --trig_cnt_out_sk_spl                   false
% 7.12/1.48  --abstr_cl_out                          false
% 7.12/1.48  
% 7.12/1.48  ------ Global Options
% 7.12/1.48  
% 7.12/1.48  --schedule                              default
% 7.12/1.48  --add_important_lit                     false
% 7.12/1.48  --prop_solver_per_cl                    1000
% 7.12/1.48  --min_unsat_core                        false
% 7.12/1.48  --soft_assumptions                      false
% 7.12/1.48  --soft_lemma_size                       3
% 7.12/1.48  --prop_impl_unit_size                   0
% 7.12/1.48  --prop_impl_unit                        []
% 7.12/1.48  --share_sel_clauses                     true
% 7.12/1.48  --reset_solvers                         false
% 7.12/1.48  --bc_imp_inh                            [conj_cone]
% 7.12/1.48  --conj_cone_tolerance                   3.
% 7.12/1.48  --extra_neg_conj                        none
% 7.12/1.48  --large_theory_mode                     true
% 7.12/1.48  --prolific_symb_bound                   200
% 7.12/1.48  --lt_threshold                          2000
% 7.12/1.48  --clause_weak_htbl                      true
% 7.12/1.48  --gc_record_bc_elim                     false
% 7.12/1.48  
% 7.12/1.48  ------ Preprocessing Options
% 7.12/1.48  
% 7.12/1.48  --preprocessing_flag                    true
% 7.12/1.48  --time_out_prep_mult                    0.1
% 7.12/1.48  --splitting_mode                        input
% 7.12/1.48  --splitting_grd                         true
% 7.12/1.48  --splitting_cvd                         false
% 7.12/1.48  --splitting_cvd_svl                     false
% 7.12/1.48  --splitting_nvd                         32
% 7.12/1.48  --sub_typing                            true
% 7.12/1.48  --prep_gs_sim                           true
% 7.12/1.48  --prep_unflatten                        true
% 7.12/1.48  --prep_res_sim                          true
% 7.12/1.48  --prep_upred                            true
% 7.12/1.48  --prep_sem_filter                       exhaustive
% 7.12/1.48  --prep_sem_filter_out                   false
% 7.12/1.48  --pred_elim                             true
% 7.12/1.48  --res_sim_input                         true
% 7.12/1.48  --eq_ax_congr_red                       true
% 7.12/1.48  --pure_diseq_elim                       true
% 7.12/1.48  --brand_transform                       false
% 7.12/1.48  --non_eq_to_eq                          false
% 7.12/1.48  --prep_def_merge                        true
% 7.12/1.48  --prep_def_merge_prop_impl              false
% 7.12/1.48  --prep_def_merge_mbd                    true
% 7.12/1.48  --prep_def_merge_tr_red                 false
% 7.12/1.48  --prep_def_merge_tr_cl                  false
% 7.12/1.48  --smt_preprocessing                     true
% 7.12/1.48  --smt_ac_axioms                         fast
% 7.12/1.48  --preprocessed_out                      false
% 7.12/1.48  --preprocessed_stats                    false
% 7.12/1.48  
% 7.12/1.48  ------ Abstraction refinement Options
% 7.12/1.48  
% 7.12/1.48  --abstr_ref                             []
% 7.12/1.48  --abstr_ref_prep                        false
% 7.12/1.48  --abstr_ref_until_sat                   false
% 7.12/1.48  --abstr_ref_sig_restrict                funpre
% 7.12/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.12/1.48  --abstr_ref_under                       []
% 7.12/1.48  
% 7.12/1.48  ------ SAT Options
% 7.12/1.48  
% 7.12/1.48  --sat_mode                              false
% 7.12/1.48  --sat_fm_restart_options                ""
% 7.12/1.48  --sat_gr_def                            false
% 7.12/1.48  --sat_epr_types                         true
% 7.12/1.48  --sat_non_cyclic_types                  false
% 7.12/1.48  --sat_finite_models                     false
% 7.12/1.48  --sat_fm_lemmas                         false
% 7.12/1.48  --sat_fm_prep                           false
% 7.12/1.48  --sat_fm_uc_incr                        true
% 7.12/1.48  --sat_out_model                         small
% 7.12/1.48  --sat_out_clauses                       false
% 7.12/1.48  
% 7.12/1.48  ------ QBF Options
% 7.12/1.48  
% 7.12/1.48  --qbf_mode                              false
% 7.12/1.48  --qbf_elim_univ                         false
% 7.12/1.48  --qbf_dom_inst                          none
% 7.12/1.48  --qbf_dom_pre_inst                      false
% 7.12/1.48  --qbf_sk_in                             false
% 7.12/1.48  --qbf_pred_elim                         true
% 7.12/1.48  --qbf_split                             512
% 7.12/1.48  
% 7.12/1.48  ------ BMC1 Options
% 7.12/1.48  
% 7.12/1.48  --bmc1_incremental                      false
% 7.12/1.48  --bmc1_axioms                           reachable_all
% 7.12/1.48  --bmc1_min_bound                        0
% 7.12/1.48  --bmc1_max_bound                        -1
% 7.12/1.48  --bmc1_max_bound_default                -1
% 7.12/1.48  --bmc1_symbol_reachability              true
% 7.12/1.48  --bmc1_property_lemmas                  false
% 7.12/1.48  --bmc1_k_induction                      false
% 7.12/1.48  --bmc1_non_equiv_states                 false
% 7.12/1.48  --bmc1_deadlock                         false
% 7.12/1.48  --bmc1_ucm                              false
% 7.12/1.48  --bmc1_add_unsat_core                   none
% 7.12/1.48  --bmc1_unsat_core_children              false
% 7.12/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.12/1.48  --bmc1_out_stat                         full
% 7.12/1.48  --bmc1_ground_init                      false
% 7.12/1.48  --bmc1_pre_inst_next_state              false
% 7.12/1.48  --bmc1_pre_inst_state                   false
% 7.12/1.48  --bmc1_pre_inst_reach_state             false
% 7.12/1.48  --bmc1_out_unsat_core                   false
% 7.12/1.48  --bmc1_aig_witness_out                  false
% 7.12/1.48  --bmc1_verbose                          false
% 7.12/1.48  --bmc1_dump_clauses_tptp                false
% 7.12/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.12/1.48  --bmc1_dump_file                        -
% 7.12/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.12/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.12/1.48  --bmc1_ucm_extend_mode                  1
% 7.12/1.48  --bmc1_ucm_init_mode                    2
% 7.12/1.48  --bmc1_ucm_cone_mode                    none
% 7.12/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.12/1.48  --bmc1_ucm_relax_model                  4
% 7.12/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.12/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.12/1.48  --bmc1_ucm_layered_model                none
% 7.12/1.48  --bmc1_ucm_max_lemma_size               10
% 7.12/1.48  
% 7.12/1.48  ------ AIG Options
% 7.12/1.48  
% 7.12/1.48  --aig_mode                              false
% 7.12/1.48  
% 7.12/1.48  ------ Instantiation Options
% 7.12/1.48  
% 7.12/1.48  --instantiation_flag                    true
% 7.12/1.48  --inst_sos_flag                         true
% 7.12/1.48  --inst_sos_phase                        true
% 7.12/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.12/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.12/1.48  --inst_lit_sel_side                     num_symb
% 7.12/1.48  --inst_solver_per_active                1400
% 7.12/1.48  --inst_solver_calls_frac                1.
% 7.12/1.48  --inst_passive_queue_type               priority_queues
% 7.12/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.12/1.48  --inst_passive_queues_freq              [25;2]
% 7.12/1.48  --inst_dismatching                      true
% 7.12/1.48  --inst_eager_unprocessed_to_passive     true
% 7.12/1.48  --inst_prop_sim_given                   true
% 7.12/1.48  --inst_prop_sim_new                     false
% 7.12/1.48  --inst_subs_new                         false
% 7.12/1.48  --inst_eq_res_simp                      false
% 7.12/1.48  --inst_subs_given                       false
% 7.12/1.48  --inst_orphan_elimination               true
% 7.12/1.48  --inst_learning_loop_flag               true
% 7.12/1.48  --inst_learning_start                   3000
% 7.12/1.48  --inst_learning_factor                  2
% 7.12/1.48  --inst_start_prop_sim_after_learn       3
% 7.12/1.48  --inst_sel_renew                        solver
% 7.12/1.48  --inst_lit_activity_flag                true
% 7.12/1.48  --inst_restr_to_given                   false
% 7.12/1.48  --inst_activity_threshold               500
% 7.12/1.48  --inst_out_proof                        true
% 7.12/1.48  
% 7.12/1.48  ------ Resolution Options
% 7.12/1.48  
% 7.12/1.48  --resolution_flag                       true
% 7.12/1.48  --res_lit_sel                           adaptive
% 7.12/1.48  --res_lit_sel_side                      none
% 7.12/1.48  --res_ordering                          kbo
% 7.12/1.48  --res_to_prop_solver                    active
% 7.12/1.48  --res_prop_simpl_new                    false
% 7.12/1.48  --res_prop_simpl_given                  true
% 7.12/1.48  --res_passive_queue_type                priority_queues
% 7.12/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.12/1.48  --res_passive_queues_freq               [15;5]
% 7.12/1.48  --res_forward_subs                      full
% 7.12/1.48  --res_backward_subs                     full
% 7.12/1.48  --res_forward_subs_resolution           true
% 7.12/1.48  --res_backward_subs_resolution          true
% 7.12/1.48  --res_orphan_elimination                true
% 7.12/1.48  --res_time_limit                        2.
% 7.12/1.48  --res_out_proof                         true
% 7.12/1.48  
% 7.12/1.48  ------ Superposition Options
% 7.12/1.48  
% 7.12/1.48  --superposition_flag                    true
% 7.12/1.48  --sup_passive_queue_type                priority_queues
% 7.12/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.12/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.12/1.48  --demod_completeness_check              fast
% 7.12/1.48  --demod_use_ground                      true
% 7.12/1.48  --sup_to_prop_solver                    passive
% 7.12/1.48  --sup_prop_simpl_new                    true
% 7.12/1.48  --sup_prop_simpl_given                  true
% 7.12/1.48  --sup_fun_splitting                     true
% 7.12/1.48  --sup_smt_interval                      50000
% 7.12/1.48  
% 7.12/1.48  ------ Superposition Simplification Setup
% 7.12/1.48  
% 7.12/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.12/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.12/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.12/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.12/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.12/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.12/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.12/1.48  --sup_immed_triv                        [TrivRules]
% 7.12/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.12/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.12/1.48  --sup_immed_bw_main                     []
% 7.12/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.12/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.12/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.12/1.48  --sup_input_bw                          []
% 7.12/1.48  
% 7.12/1.48  ------ Combination Options
% 7.12/1.48  
% 7.12/1.48  --comb_res_mult                         3
% 7.12/1.48  --comb_sup_mult                         2
% 7.12/1.48  --comb_inst_mult                        10
% 7.12/1.48  
% 7.12/1.48  ------ Debug Options
% 7.12/1.48  
% 7.12/1.48  --dbg_backtrace                         false
% 7.12/1.48  --dbg_dump_prop_clauses                 false
% 7.12/1.48  --dbg_dump_prop_clauses_file            -
% 7.12/1.48  --dbg_out_stat                          false
% 7.12/1.48  ------ Parsing...
% 7.12/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.12/1.48  
% 7.12/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.12/1.48  
% 7.12/1.48  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.12/1.48  
% 7.12/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.12/1.48  ------ Proving...
% 7.12/1.48  ------ Problem Properties 
% 7.12/1.48  
% 7.12/1.48  
% 7.12/1.48  clauses                                 25
% 7.12/1.48  conjectures                             3
% 7.12/1.48  EPR                                     3
% 7.12/1.48  Horn                                    21
% 7.12/1.48  unary                                   9
% 7.12/1.48  binary                                  8
% 7.12/1.48  lits                                    50
% 7.12/1.48  lits eq                                 14
% 7.12/1.48  fd_pure                                 0
% 7.12/1.48  fd_pseudo                               0
% 7.12/1.48  fd_cond                                 1
% 7.12/1.48  fd_pseudo_cond                          2
% 7.12/1.48  AC symbols                              0
% 7.12/1.48  
% 7.12/1.48  ------ Schedule dynamic 5 is on 
% 7.12/1.48  
% 7.12/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.12/1.48  
% 7.12/1.48  
% 7.12/1.48  ------ 
% 7.12/1.48  Current options:
% 7.12/1.48  ------ 
% 7.12/1.48  
% 7.12/1.48  ------ Input Options
% 7.12/1.48  
% 7.12/1.48  --out_options                           all
% 7.12/1.48  --tptp_safe_out                         true
% 7.12/1.48  --problem_path                          ""
% 7.12/1.48  --include_path                          ""
% 7.12/1.48  --clausifier                            res/vclausify_rel
% 7.12/1.48  --clausifier_options                    ""
% 7.12/1.48  --stdin                                 false
% 7.12/1.48  --stats_out                             all
% 7.12/1.48  
% 7.12/1.48  ------ General Options
% 7.12/1.48  
% 7.12/1.48  --fof                                   false
% 7.12/1.48  --time_out_real                         305.
% 7.12/1.48  --time_out_virtual                      -1.
% 7.12/1.48  --symbol_type_check                     false
% 7.12/1.48  --clausify_out                          false
% 7.12/1.48  --sig_cnt_out                           false
% 7.12/1.48  --trig_cnt_out                          false
% 7.12/1.48  --trig_cnt_out_tolerance                1.
% 7.12/1.48  --trig_cnt_out_sk_spl                   false
% 7.12/1.48  --abstr_cl_out                          false
% 7.12/1.48  
% 7.12/1.48  ------ Global Options
% 7.12/1.48  
% 7.12/1.48  --schedule                              default
% 7.12/1.48  --add_important_lit                     false
% 7.12/1.48  --prop_solver_per_cl                    1000
% 7.12/1.48  --min_unsat_core                        false
% 7.12/1.48  --soft_assumptions                      false
% 7.12/1.48  --soft_lemma_size                       3
% 7.12/1.48  --prop_impl_unit_size                   0
% 7.12/1.48  --prop_impl_unit                        []
% 7.12/1.48  --share_sel_clauses                     true
% 7.12/1.48  --reset_solvers                         false
% 7.12/1.48  --bc_imp_inh                            [conj_cone]
% 7.12/1.48  --conj_cone_tolerance                   3.
% 7.12/1.48  --extra_neg_conj                        none
% 7.12/1.48  --large_theory_mode                     true
% 7.12/1.48  --prolific_symb_bound                   200
% 7.12/1.48  --lt_threshold                          2000
% 7.12/1.48  --clause_weak_htbl                      true
% 7.12/1.48  --gc_record_bc_elim                     false
% 7.12/1.48  
% 7.12/1.48  ------ Preprocessing Options
% 7.12/1.48  
% 7.12/1.48  --preprocessing_flag                    true
% 7.12/1.48  --time_out_prep_mult                    0.1
% 7.12/1.48  --splitting_mode                        input
% 7.12/1.48  --splitting_grd                         true
% 7.12/1.48  --splitting_cvd                         false
% 7.12/1.48  --splitting_cvd_svl                     false
% 7.12/1.48  --splitting_nvd                         32
% 7.12/1.48  --sub_typing                            true
% 7.12/1.48  --prep_gs_sim                           true
% 7.12/1.48  --prep_unflatten                        true
% 7.12/1.48  --prep_res_sim                          true
% 7.12/1.48  --prep_upred                            true
% 7.12/1.48  --prep_sem_filter                       exhaustive
% 7.12/1.48  --prep_sem_filter_out                   false
% 7.12/1.48  --pred_elim                             true
% 7.12/1.48  --res_sim_input                         true
% 7.12/1.48  --eq_ax_congr_red                       true
% 7.12/1.48  --pure_diseq_elim                       true
% 7.12/1.48  --brand_transform                       false
% 7.12/1.48  --non_eq_to_eq                          false
% 7.12/1.48  --prep_def_merge                        true
% 7.12/1.48  --prep_def_merge_prop_impl              false
% 7.12/1.48  --prep_def_merge_mbd                    true
% 7.12/1.48  --prep_def_merge_tr_red                 false
% 7.12/1.48  --prep_def_merge_tr_cl                  false
% 7.12/1.48  --smt_preprocessing                     true
% 7.12/1.48  --smt_ac_axioms                         fast
% 7.12/1.48  --preprocessed_out                      false
% 7.12/1.48  --preprocessed_stats                    false
% 7.12/1.48  
% 7.12/1.48  ------ Abstraction refinement Options
% 7.12/1.48  
% 7.12/1.48  --abstr_ref                             []
% 7.12/1.48  --abstr_ref_prep                        false
% 7.12/1.48  --abstr_ref_until_sat                   false
% 7.12/1.48  --abstr_ref_sig_restrict                funpre
% 7.12/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.12/1.48  --abstr_ref_under                       []
% 7.12/1.48  
% 7.12/1.48  ------ SAT Options
% 7.12/1.48  
% 7.12/1.48  --sat_mode                              false
% 7.12/1.48  --sat_fm_restart_options                ""
% 7.12/1.48  --sat_gr_def                            false
% 7.12/1.48  --sat_epr_types                         true
% 7.12/1.48  --sat_non_cyclic_types                  false
% 7.12/1.48  --sat_finite_models                     false
% 7.12/1.48  --sat_fm_lemmas                         false
% 7.12/1.48  --sat_fm_prep                           false
% 7.12/1.48  --sat_fm_uc_incr                        true
% 7.12/1.48  --sat_out_model                         small
% 7.12/1.48  --sat_out_clauses                       false
% 7.12/1.48  
% 7.12/1.48  ------ QBF Options
% 7.12/1.48  
% 7.12/1.48  --qbf_mode                              false
% 7.12/1.48  --qbf_elim_univ                         false
% 7.12/1.48  --qbf_dom_inst                          none
% 7.12/1.48  --qbf_dom_pre_inst                      false
% 7.12/1.48  --qbf_sk_in                             false
% 7.12/1.48  --qbf_pred_elim                         true
% 7.12/1.48  --qbf_split                             512
% 7.12/1.48  
% 7.12/1.48  ------ BMC1 Options
% 7.12/1.48  
% 7.12/1.48  --bmc1_incremental                      false
% 7.12/1.48  --bmc1_axioms                           reachable_all
% 7.12/1.48  --bmc1_min_bound                        0
% 7.12/1.48  --bmc1_max_bound                        -1
% 7.12/1.48  --bmc1_max_bound_default                -1
% 7.12/1.48  --bmc1_symbol_reachability              true
% 7.12/1.48  --bmc1_property_lemmas                  false
% 7.12/1.48  --bmc1_k_induction                      false
% 7.12/1.48  --bmc1_non_equiv_states                 false
% 7.12/1.48  --bmc1_deadlock                         false
% 7.12/1.48  --bmc1_ucm                              false
% 7.12/1.48  --bmc1_add_unsat_core                   none
% 7.12/1.48  --bmc1_unsat_core_children              false
% 7.12/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.12/1.48  --bmc1_out_stat                         full
% 7.12/1.48  --bmc1_ground_init                      false
% 7.12/1.48  --bmc1_pre_inst_next_state              false
% 7.12/1.48  --bmc1_pre_inst_state                   false
% 7.12/1.48  --bmc1_pre_inst_reach_state             false
% 7.12/1.48  --bmc1_out_unsat_core                   false
% 7.12/1.48  --bmc1_aig_witness_out                  false
% 7.12/1.48  --bmc1_verbose                          false
% 7.12/1.48  --bmc1_dump_clauses_tptp                false
% 7.12/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.12/1.48  --bmc1_dump_file                        -
% 7.12/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.12/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.12/1.48  --bmc1_ucm_extend_mode                  1
% 7.12/1.48  --bmc1_ucm_init_mode                    2
% 7.12/1.48  --bmc1_ucm_cone_mode                    none
% 7.12/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.12/1.48  --bmc1_ucm_relax_model                  4
% 7.12/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.12/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.12/1.48  --bmc1_ucm_layered_model                none
% 7.12/1.48  --bmc1_ucm_max_lemma_size               10
% 7.12/1.48  
% 7.12/1.48  ------ AIG Options
% 7.12/1.48  
% 7.12/1.48  --aig_mode                              false
% 7.12/1.48  
% 7.12/1.48  ------ Instantiation Options
% 7.12/1.48  
% 7.12/1.48  --instantiation_flag                    true
% 7.12/1.48  --inst_sos_flag                         true
% 7.12/1.48  --inst_sos_phase                        true
% 7.12/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.12/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.12/1.48  --inst_lit_sel_side                     none
% 7.12/1.48  --inst_solver_per_active                1400
% 7.12/1.48  --inst_solver_calls_frac                1.
% 7.12/1.48  --inst_passive_queue_type               priority_queues
% 7.12/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.12/1.48  --inst_passive_queues_freq              [25;2]
% 7.12/1.48  --inst_dismatching                      true
% 7.12/1.48  --inst_eager_unprocessed_to_passive     true
% 7.12/1.48  --inst_prop_sim_given                   true
% 7.12/1.48  --inst_prop_sim_new                     false
% 7.12/1.48  --inst_subs_new                         false
% 7.12/1.48  --inst_eq_res_simp                      false
% 7.12/1.48  --inst_subs_given                       false
% 7.12/1.48  --inst_orphan_elimination               true
% 7.12/1.48  --inst_learning_loop_flag               true
% 7.12/1.48  --inst_learning_start                   3000
% 7.12/1.48  --inst_learning_factor                  2
% 7.12/1.48  --inst_start_prop_sim_after_learn       3
% 7.12/1.48  --inst_sel_renew                        solver
% 7.12/1.48  --inst_lit_activity_flag                true
% 7.12/1.48  --inst_restr_to_given                   false
% 7.12/1.48  --inst_activity_threshold               500
% 7.12/1.48  --inst_out_proof                        true
% 7.12/1.48  
% 7.12/1.48  ------ Resolution Options
% 7.12/1.48  
% 7.12/1.48  --resolution_flag                       false
% 7.12/1.48  --res_lit_sel                           adaptive
% 7.12/1.48  --res_lit_sel_side                      none
% 7.12/1.48  --res_ordering                          kbo
% 7.12/1.48  --res_to_prop_solver                    active
% 7.12/1.48  --res_prop_simpl_new                    false
% 7.12/1.48  --res_prop_simpl_given                  true
% 7.12/1.48  --res_passive_queue_type                priority_queues
% 7.12/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.12/1.48  --res_passive_queues_freq               [15;5]
% 7.12/1.48  --res_forward_subs                      full
% 7.12/1.48  --res_backward_subs                     full
% 7.12/1.48  --res_forward_subs_resolution           true
% 7.12/1.48  --res_backward_subs_resolution          true
% 7.12/1.48  --res_orphan_elimination                true
% 7.12/1.48  --res_time_limit                        2.
% 7.12/1.48  --res_out_proof                         true
% 7.12/1.48  
% 7.12/1.48  ------ Superposition Options
% 7.12/1.48  
% 7.12/1.48  --superposition_flag                    true
% 7.12/1.48  --sup_passive_queue_type                priority_queues
% 7.12/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.12/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.12/1.48  --demod_completeness_check              fast
% 7.12/1.48  --demod_use_ground                      true
% 7.12/1.48  --sup_to_prop_solver                    passive
% 7.12/1.48  --sup_prop_simpl_new                    true
% 7.12/1.48  --sup_prop_simpl_given                  true
% 7.12/1.48  --sup_fun_splitting                     true
% 7.12/1.48  --sup_smt_interval                      50000
% 7.12/1.48  
% 7.12/1.48  ------ Superposition Simplification Setup
% 7.12/1.48  
% 7.12/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.12/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.12/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.12/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.12/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.12/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.12/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.12/1.48  --sup_immed_triv                        [TrivRules]
% 7.12/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.12/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.12/1.48  --sup_immed_bw_main                     []
% 7.12/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.12/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.12/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.12/1.48  --sup_input_bw                          []
% 7.12/1.48  
% 7.12/1.48  ------ Combination Options
% 7.12/1.48  
% 7.12/1.48  --comb_res_mult                         3
% 7.12/1.48  --comb_sup_mult                         2
% 7.12/1.48  --comb_inst_mult                        10
% 7.12/1.48  
% 7.12/1.48  ------ Debug Options
% 7.12/1.48  
% 7.12/1.48  --dbg_backtrace                         false
% 7.12/1.48  --dbg_dump_prop_clauses                 false
% 7.12/1.48  --dbg_dump_prop_clauses_file            -
% 7.12/1.48  --dbg_out_stat                          false
% 7.12/1.48  
% 7.12/1.48  
% 7.12/1.48  
% 7.12/1.48  
% 7.12/1.48  ------ Proving...
% 7.12/1.48  
% 7.12/1.48  
% 7.12/1.48  % SZS status Theorem for theBenchmark.p
% 7.12/1.48  
% 7.12/1.48   Resolution empty clause
% 7.12/1.48  
% 7.12/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.12/1.48  
% 7.12/1.48  fof(f7,axiom,(
% 7.12/1.48    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 7.12/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.48  
% 7.12/1.48  fof(f65,plain,(
% 7.12/1.48    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 7.12/1.48    inference(cnf_transformation,[],[f7])).
% 7.12/1.48  
% 7.12/1.48  fof(f8,axiom,(
% 7.12/1.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.12/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.48  
% 7.12/1.48  fof(f47,plain,(
% 7.12/1.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.12/1.48    inference(nnf_transformation,[],[f8])).
% 7.12/1.48  
% 7.12/1.48  fof(f66,plain,(
% 7.12/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.12/1.48    inference(cnf_transformation,[],[f47])).
% 7.12/1.48  
% 7.12/1.48  fof(f11,axiom,(
% 7.12/1.48    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 7.12/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.48  
% 7.12/1.48  fof(f28,plain,(
% 7.12/1.48    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 7.12/1.48    inference(ennf_transformation,[],[f11])).
% 7.12/1.48  
% 7.12/1.48  fof(f71,plain,(
% 7.12/1.48    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 7.12/1.48    inference(cnf_transformation,[],[f28])).
% 7.12/1.48  
% 7.12/1.48  fof(f20,conjecture,(
% 7.12/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 7.12/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.48  
% 7.12/1.48  fof(f21,negated_conjecture,(
% 7.12/1.48    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 7.12/1.48    inference(negated_conjecture,[],[f20])).
% 7.12/1.48  
% 7.12/1.48  fof(f22,plain,(
% 7.12/1.48    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 7.12/1.48    inference(pure_predicate_removal,[],[f21])).
% 7.12/1.48  
% 7.12/1.48  fof(f39,plain,(
% 7.12/1.48    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 7.12/1.48    inference(ennf_transformation,[],[f22])).
% 7.12/1.48  
% 7.12/1.48  fof(f40,plain,(
% 7.12/1.48    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 7.12/1.48    inference(flattening,[],[f39])).
% 7.12/1.48  
% 7.12/1.48  fof(f51,plain,(
% 7.12/1.48    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1))) & k1_xboole_0 != sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_1(sK4))),
% 7.12/1.48    introduced(choice_axiom,[])).
% 7.12/1.48  
% 7.12/1.48  fof(f52,plain,(
% 7.12/1.48    ~r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1))) & k1_xboole_0 != sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_1(sK4)),
% 7.12/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f40,f51])).
% 7.12/1.48  
% 7.12/1.48  fof(f84,plain,(
% 7.12/1.48    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))),
% 7.12/1.48    inference(cnf_transformation,[],[f52])).
% 7.12/1.48  
% 7.12/1.48  fof(f2,axiom,(
% 7.12/1.48    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.12/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.48  
% 7.12/1.48  fof(f56,plain,(
% 7.12/1.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.12/1.48    inference(cnf_transformation,[],[f2])).
% 7.12/1.48  
% 7.12/1.48  fof(f3,axiom,(
% 7.12/1.48    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.12/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.48  
% 7.12/1.48  fof(f57,plain,(
% 7.12/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.12/1.48    inference(cnf_transformation,[],[f3])).
% 7.12/1.48  
% 7.12/1.48  fof(f4,axiom,(
% 7.12/1.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.12/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.48  
% 7.12/1.48  fof(f58,plain,(
% 7.12/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.12/1.48    inference(cnf_transformation,[],[f4])).
% 7.12/1.48  
% 7.12/1.48  fof(f87,plain,(
% 7.12/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 7.12/1.48    inference(definition_unfolding,[],[f57,f58])).
% 7.12/1.48  
% 7.12/1.48  fof(f88,plain,(
% 7.12/1.48    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 7.12/1.48    inference(definition_unfolding,[],[f56,f87])).
% 7.12/1.48  
% 7.12/1.48  fof(f94,plain,(
% 7.12/1.48    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))),
% 7.12/1.48    inference(definition_unfolding,[],[f84,f88])).
% 7.12/1.48  
% 7.12/1.48  fof(f15,axiom,(
% 7.12/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.12/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.48  
% 7.12/1.48  fof(f24,plain,(
% 7.12/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.12/1.48    inference(pure_predicate_removal,[],[f15])).
% 7.12/1.48  
% 7.12/1.48  fof(f33,plain,(
% 7.12/1.48    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.12/1.48    inference(ennf_transformation,[],[f24])).
% 7.12/1.48  
% 7.12/1.48  fof(f75,plain,(
% 7.12/1.48    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.12/1.48    inference(cnf_transformation,[],[f33])).
% 7.12/1.48  
% 7.12/1.48  fof(f10,axiom,(
% 7.12/1.48    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 7.12/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.48  
% 7.12/1.48  fof(f27,plain,(
% 7.12/1.48    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.12/1.48    inference(ennf_transformation,[],[f10])).
% 7.12/1.48  
% 7.12/1.48  fof(f48,plain,(
% 7.12/1.48    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.12/1.48    inference(nnf_transformation,[],[f27])).
% 7.12/1.48  
% 7.12/1.48  fof(f69,plain,(
% 7.12/1.48    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.12/1.48    inference(cnf_transformation,[],[f48])).
% 7.12/1.48  
% 7.12/1.48  fof(f14,axiom,(
% 7.12/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.12/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.48  
% 7.12/1.48  fof(f32,plain,(
% 7.12/1.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.12/1.48    inference(ennf_transformation,[],[f14])).
% 7.12/1.48  
% 7.12/1.48  fof(f74,plain,(
% 7.12/1.48    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.12/1.48    inference(cnf_transformation,[],[f32])).
% 7.12/1.48  
% 7.12/1.48  fof(f5,axiom,(
% 7.12/1.48    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 7.12/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.48  
% 7.12/1.48  fof(f43,plain,(
% 7.12/1.48    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 7.12/1.48    inference(nnf_transformation,[],[f5])).
% 7.12/1.48  
% 7.12/1.48  fof(f44,plain,(
% 7.12/1.48    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 7.12/1.48    inference(flattening,[],[f43])).
% 7.12/1.48  
% 7.12/1.48  fof(f59,plain,(
% 7.12/1.48    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 7.12/1.48    inference(cnf_transformation,[],[f44])).
% 7.12/1.48  
% 7.12/1.48  fof(f91,plain,(
% 7.12/1.48    ( ! [X0,X1] : (k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))) )),
% 7.12/1.48    inference(definition_unfolding,[],[f59,f88,f88])).
% 7.12/1.48  
% 7.12/1.48  fof(f86,plain,(
% 7.12/1.48    ~r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1)))),
% 7.12/1.48    inference(cnf_transformation,[],[f52])).
% 7.12/1.48  
% 7.12/1.48  fof(f93,plain,(
% 7.12/1.48    ~r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)))),
% 7.12/1.48    inference(definition_unfolding,[],[f86,f88,f88])).
% 7.12/1.48  
% 7.12/1.48  fof(f12,axiom,(
% 7.12/1.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 7.12/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.48  
% 7.12/1.48  fof(f29,plain,(
% 7.12/1.48    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.12/1.48    inference(ennf_transformation,[],[f12])).
% 7.12/1.48  
% 7.12/1.48  fof(f30,plain,(
% 7.12/1.48    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.12/1.48    inference(flattening,[],[f29])).
% 7.12/1.48  
% 7.12/1.48  fof(f72,plain,(
% 7.12/1.48    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.12/1.48    inference(cnf_transformation,[],[f30])).
% 7.12/1.48  
% 7.12/1.48  fof(f92,plain,(
% 7.12/1.48    ( ! [X0,X1] : (k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1) | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.12/1.48    inference(definition_unfolding,[],[f72,f88,f88])).
% 7.12/1.48  
% 7.12/1.48  fof(f83,plain,(
% 7.12/1.48    v1_funct_1(sK4)),
% 7.12/1.48    inference(cnf_transformation,[],[f52])).
% 7.12/1.48  
% 7.12/1.48  fof(f18,axiom,(
% 7.12/1.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 7.12/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.48  
% 7.12/1.48  fof(f36,plain,(
% 7.12/1.48    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.12/1.48    inference(ennf_transformation,[],[f18])).
% 7.12/1.48  
% 7.12/1.48  fof(f78,plain,(
% 7.12/1.48    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.12/1.48    inference(cnf_transformation,[],[f36])).
% 7.12/1.48  
% 7.12/1.48  fof(f1,axiom,(
% 7.12/1.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.12/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.48  
% 7.12/1.48  fof(f41,plain,(
% 7.12/1.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.12/1.48    inference(nnf_transformation,[],[f1])).
% 7.12/1.48  
% 7.12/1.48  fof(f42,plain,(
% 7.12/1.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.12/1.48    inference(flattening,[],[f41])).
% 7.12/1.48  
% 7.12/1.48  fof(f55,plain,(
% 7.12/1.48    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.12/1.48    inference(cnf_transformation,[],[f42])).
% 7.12/1.48  
% 7.12/1.48  fof(f53,plain,(
% 7.12/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.12/1.48    inference(cnf_transformation,[],[f42])).
% 7.12/1.48  
% 7.12/1.48  fof(f96,plain,(
% 7.12/1.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.12/1.48    inference(equality_resolution,[],[f53])).
% 7.12/1.48  
% 7.12/1.48  fof(f13,axiom,(
% 7.12/1.48    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 7.12/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.48  
% 7.12/1.48  fof(f31,plain,(
% 7.12/1.48    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 7.12/1.48    inference(ennf_transformation,[],[f13])).
% 7.12/1.48  
% 7.12/1.48  fof(f73,plain,(
% 7.12/1.48    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 7.12/1.48    inference(cnf_transformation,[],[f31])).
% 7.12/1.48  
% 7.12/1.48  fof(f19,axiom,(
% 7.12/1.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 7.12/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.48  
% 7.12/1.48  fof(f23,plain,(
% 7.12/1.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))))),
% 7.12/1.48    inference(pure_predicate_removal,[],[f19])).
% 7.12/1.48  
% 7.12/1.48  fof(f37,plain,(
% 7.12/1.48    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 7.12/1.48    inference(ennf_transformation,[],[f23])).
% 7.12/1.48  
% 7.12/1.48  fof(f38,plain,(
% 7.12/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.12/1.48    inference(flattening,[],[f37])).
% 7.12/1.48  
% 7.12/1.48  fof(f49,plain,(
% 7.12/1.48    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) => (~r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1) & r2_hidden(sK0(X0,X1,X2),X0)))),
% 7.12/1.48    introduced(choice_axiom,[])).
% 7.12/1.48  
% 7.12/1.48  fof(f50,plain,(
% 7.12/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) | (~r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.12/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f49])).
% 7.12/1.48  
% 7.12/1.48  fof(f81,plain,(
% 7.12/1.48    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_hidden(sK0(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.12/1.48    inference(cnf_transformation,[],[f50])).
% 7.12/1.48  
% 7.12/1.48  fof(f102,plain,(
% 7.12/1.48    ( ! [X2,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | r2_hidden(sK0(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.12/1.48    inference(equality_resolution,[],[f81])).
% 7.12/1.48  
% 7.12/1.48  fof(f6,axiom,(
% 7.12/1.48    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.12/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.48  
% 7.12/1.48  fof(f45,plain,(
% 7.12/1.48    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.12/1.48    inference(nnf_transformation,[],[f6])).
% 7.12/1.48  
% 7.12/1.48  fof(f46,plain,(
% 7.12/1.48    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.12/1.48    inference(flattening,[],[f45])).
% 7.12/1.48  
% 7.12/1.48  fof(f63,plain,(
% 7.12/1.48    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 7.12/1.48    inference(cnf_transformation,[],[f46])).
% 7.12/1.48  
% 7.12/1.48  fof(f100,plain,(
% 7.12/1.48    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 7.12/1.48    inference(equality_resolution,[],[f63])).
% 7.12/1.48  
% 7.12/1.48  fof(f17,axiom,(
% 7.12/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 7.12/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.48  
% 7.12/1.48  fof(f35,plain,(
% 7.12/1.48    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.12/1.48    inference(ennf_transformation,[],[f17])).
% 7.12/1.48  
% 7.12/1.48  fof(f77,plain,(
% 7.12/1.48    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.12/1.48    inference(cnf_transformation,[],[f35])).
% 7.12/1.48  
% 7.12/1.48  fof(f16,axiom,(
% 7.12/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 7.12/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.48  
% 7.12/1.48  fof(f34,plain,(
% 7.12/1.48    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.12/1.48    inference(ennf_transformation,[],[f16])).
% 7.12/1.48  
% 7.12/1.48  fof(f76,plain,(
% 7.12/1.48    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.12/1.48    inference(cnf_transformation,[],[f34])).
% 7.12/1.48  
% 7.12/1.48  fof(f64,plain,(
% 7.12/1.48    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 7.12/1.48    inference(cnf_transformation,[],[f46])).
% 7.12/1.48  
% 7.12/1.48  fof(f99,plain,(
% 7.12/1.48    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 7.12/1.48    inference(equality_resolution,[],[f64])).
% 7.12/1.48  
% 7.12/1.48  cnf(c_9,plain,
% 7.12/1.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 7.12/1.48      inference(cnf_transformation,[],[f65]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_1364,plain,
% 7.12/1.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 7.12/1.48      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_11,plain,
% 7.12/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.12/1.48      inference(cnf_transformation,[],[f66]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_1362,plain,
% 7.12/1.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.12/1.48      | r1_tarski(X0,X1) = iProver_top ),
% 7.12/1.48      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_2388,plain,
% 7.12/1.48      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.12/1.48      inference(superposition,[status(thm)],[c_1364,c_1362]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_15,plain,
% 7.12/1.48      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 7.12/1.48      inference(cnf_transformation,[],[f71]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_1361,plain,
% 7.12/1.48      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) = iProver_top
% 7.12/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.12/1.48      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_29,negated_conjecture,
% 7.12/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
% 7.12/1.48      inference(cnf_transformation,[],[f94]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_1355,plain,
% 7.12/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) = iProver_top ),
% 7.12/1.48      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_19,plain,
% 7.12/1.48      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.12/1.48      inference(cnf_transformation,[],[f75]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_14,plain,
% 7.12/1.48      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 7.12/1.48      inference(cnf_transformation,[],[f69]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_347,plain,
% 7.12/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.12/1.48      | r1_tarski(k1_relat_1(X0),X1)
% 7.12/1.48      | ~ v1_relat_1(X0) ),
% 7.12/1.48      inference(resolution,[status(thm)],[c_19,c_14]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_18,plain,
% 7.12/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 7.12/1.48      inference(cnf_transformation,[],[f74]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_351,plain,
% 7.12/1.48      ( r1_tarski(k1_relat_1(X0),X1)
% 7.12/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.12/1.48      inference(global_propositional_subsumption,[status(thm)],[c_347,c_18]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_352,plain,
% 7.12/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.12/1.48      | r1_tarski(k1_relat_1(X0),X1) ),
% 7.12/1.48      inference(renaming,[status(thm)],[c_351]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_1354,plain,
% 7.12/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.12/1.48      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 7.12/1.48      inference(predicate_to_equality,[status(thm)],[c_352]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_1854,plain,
% 7.12/1.48      ( r1_tarski(k1_relat_1(sK4),k2_enumset1(sK1,sK1,sK1,sK1)) = iProver_top ),
% 7.12/1.48      inference(superposition,[status(thm)],[c_1355,c_1354]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_5,plain,
% 7.12/1.48      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
% 7.12/1.48      | k2_enumset1(X1,X1,X1,X1) = X0
% 7.12/1.48      | k1_xboole_0 = X0 ),
% 7.12/1.48      inference(cnf_transformation,[],[f91]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_1365,plain,
% 7.12/1.48      ( k2_enumset1(X0,X0,X0,X0) = X1
% 7.12/1.48      | k1_xboole_0 = X1
% 7.12/1.48      | r1_tarski(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
% 7.12/1.48      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_3652,plain,
% 7.12/1.48      ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK4)
% 7.12/1.48      | k1_relat_1(sK4) = k1_xboole_0 ),
% 7.12/1.48      inference(superposition,[status(thm)],[c_1854,c_1365]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_27,negated_conjecture,
% 7.12/1.48      ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) ),
% 7.12/1.48      inference(cnf_transformation,[],[f93]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_1422,plain,
% 7.12/1.48      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(sK4) ),
% 7.12/1.48      inference(instantiation,[status(thm)],[c_18]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_1509,plain,
% 7.12/1.48      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))
% 7.12/1.48      | v1_relat_1(sK4) ),
% 7.12/1.48      inference(instantiation,[status(thm)],[c_1422]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_16,plain,
% 7.12/1.48      ( ~ v1_funct_1(X0)
% 7.12/1.48      | ~ v1_relat_1(X0)
% 7.12/1.48      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 7.12/1.48      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
% 7.12/1.48      inference(cnf_transformation,[],[f92]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_30,negated_conjecture,
% 7.12/1.48      ( v1_funct_1(sK4) ),
% 7.12/1.48      inference(cnf_transformation,[],[f83]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_398,plain,
% 7.12/1.48      ( ~ v1_relat_1(X0)
% 7.12/1.48      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 7.12/1.48      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
% 7.12/1.48      | sK4 != X0 ),
% 7.12/1.48      inference(resolution_lifted,[status(thm)],[c_16,c_30]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_399,plain,
% 7.12/1.48      ( ~ v1_relat_1(sK4)
% 7.12/1.48      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK4)
% 7.12/1.48      | k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k2_relat_1(sK4) ),
% 7.12/1.48      inference(unflattening,[status(thm)],[c_398]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_1353,plain,
% 7.12/1.48      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK4)
% 7.12/1.48      | k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k2_relat_1(sK4)
% 7.12/1.48      | v1_relat_1(sK4) != iProver_top ),
% 7.12/1.48      inference(predicate_to_equality,[status(thm)],[c_399]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_1560,plain,
% 7.12/1.48      ( k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k2_relat_1(sK4)
% 7.12/1.48      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK4) ),
% 7.12/1.48      inference(global_propositional_subsumption,
% 7.12/1.48                [status(thm)],
% 7.12/1.48                [c_1353,c_29,c_399,c_1509]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_1561,plain,
% 7.12/1.48      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK4)
% 7.12/1.48      | k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k2_relat_1(sK4) ),
% 7.12/1.48      inference(renaming,[status(thm)],[c_1560]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_1562,plain,
% 7.12/1.48      ( k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) = k2_relat_1(sK4)
% 7.12/1.48      | k2_enumset1(sK1,sK1,sK1,sK1) != k1_relat_1(sK4) ),
% 7.12/1.48      inference(instantiation,[status(thm)],[c_1561]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_22,plain,
% 7.12/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.12/1.48      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 7.12/1.48      inference(cnf_transformation,[],[f78]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_1592,plain,
% 7.12/1.48      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))
% 7.12/1.48      | k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3) = k9_relat_1(sK4,sK3) ),
% 7.12/1.48      inference(instantiation,[status(thm)],[c_22]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_1857,plain,
% 7.12/1.48      ( r1_tarski(k1_relat_1(sK4),k2_enumset1(sK1,sK1,sK1,sK1)) ),
% 7.12/1.48      inference(predicate_to_equality_rev,[status(thm)],[c_1854]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_856,plain,
% 7.12/1.48      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.12/1.48      theory(equality) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_1400,plain,
% 7.12/1.48      ( ~ r1_tarski(X0,X1)
% 7.12/1.48      | r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)))
% 7.12/1.48      | k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3) != X0
% 7.12/1.48      | k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) != X1 ),
% 7.12/1.48      inference(instantiation,[status(thm)],[c_856]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_1471,plain,
% 7.12/1.48      ( r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)))
% 7.12/1.48      | ~ r1_tarski(k9_relat_1(sK4,sK3),X0)
% 7.12/1.48      | k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3) != k9_relat_1(sK4,sK3)
% 7.12/1.48      | k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) != X0 ),
% 7.12/1.48      inference(instantiation,[status(thm)],[c_1400]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_1877,plain,
% 7.12/1.48      ( r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)))
% 7.12/1.48      | ~ r1_tarski(k9_relat_1(sK4,sK3),k2_relat_1(sK4))
% 7.12/1.48      | k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3) != k9_relat_1(sK4,sK3)
% 7.12/1.48      | k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) != k2_relat_1(sK4) ),
% 7.12/1.48      inference(instantiation,[status(thm)],[c_1471]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_2362,plain,
% 7.12/1.48      ( r1_tarski(k9_relat_1(sK4,sK3),k2_relat_1(sK4)) | ~ v1_relat_1(sK4) ),
% 7.12/1.48      inference(instantiation,[status(thm)],[c_15]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_0,plain,
% 7.12/1.48      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.12/1.48      inference(cnf_transformation,[],[f55]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_1830,plain,
% 7.12/1.48      ( ~ r1_tarski(X0,k1_relat_1(sK4))
% 7.12/1.48      | ~ r1_tarski(k1_relat_1(sK4),X0)
% 7.12/1.48      | k1_relat_1(sK4) = X0 ),
% 7.12/1.48      inference(instantiation,[status(thm)],[c_0]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_2443,plain,
% 7.12/1.48      ( ~ r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4))
% 7.12/1.48      | k1_relat_1(sK4) = k1_relat_1(sK4) ),
% 7.12/1.48      inference(instantiation,[status(thm)],[c_1830]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_2,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f96]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_2639,plain,
% 7.12/1.48      ( r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) ),
% 7.12/1.48      inference(instantiation,[status(thm)],[c_2]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_1916,plain,
% 7.12/1.48      ( ~ r1_tarski(k1_relat_1(X0),k2_enumset1(X1,X1,X1,X1))
% 7.12/1.48      | k2_enumset1(X1,X1,X1,X1) = k1_relat_1(X0)
% 7.12/1.48      | k1_xboole_0 = k1_relat_1(X0) ),
% 7.12/1.48      inference(instantiation,[status(thm)],[c_5]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_3305,plain,
% 7.12/1.48      ( ~ r1_tarski(k1_relat_1(sK4),k2_enumset1(sK1,sK1,sK1,sK1))
% 7.12/1.48      | k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK4)
% 7.12/1.48      | k1_xboole_0 = k1_relat_1(sK4) ),
% 7.12/1.48      inference(instantiation,[status(thm)],[c_1916]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_855,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_1836,plain,
% 7.12/1.48      ( X0 != X1 | k1_relat_1(sK4) != X1 | k1_relat_1(sK4) = X0 ),
% 7.12/1.48      inference(instantiation,[status(thm)],[c_855]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_2460,plain,
% 7.12/1.48      ( X0 != k1_relat_1(sK4)
% 7.12/1.48      | k1_relat_1(sK4) = X0
% 7.12/1.48      | k1_relat_1(sK4) != k1_relat_1(sK4) ),
% 7.12/1.48      inference(instantiation,[status(thm)],[c_1836]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_3593,plain,
% 7.12/1.48      ( k1_relat_1(sK4) != k1_relat_1(sK4)
% 7.12/1.48      | k1_relat_1(sK4) = k1_xboole_0
% 7.12/1.48      | k1_xboole_0 != k1_relat_1(sK4) ),
% 7.12/1.48      inference(instantiation,[status(thm)],[c_2460]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_4002,plain,
% 7.12/1.48      ( k1_relat_1(sK4) = k1_xboole_0 ),
% 7.12/1.48      inference(global_propositional_subsumption,
% 7.12/1.48                [status(thm)],
% 7.12/1.48                [c_3652,c_29,c_27,c_1509,c_1562,c_1592,c_1857,c_1877,c_2362,
% 7.12/1.48                 c_2443,c_2639,c_3305,c_3593]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_17,plain,
% 7.12/1.48      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 7.12/1.48      inference(cnf_transformation,[],[f73]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_24,plain,
% 7.12/1.48      ( r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 7.12/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 7.12/1.48      | ~ v1_funct_1(X0)
% 7.12/1.48      | ~ v1_relat_1(X0) ),
% 7.12/1.48      inference(cnf_transformation,[],[f102]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_368,plain,
% 7.12/1.48      ( r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 7.12/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 7.12/1.48      | ~ v1_relat_1(X0)
% 7.12/1.48      | sK4 != X0 ),
% 7.12/1.48      inference(resolution_lifted,[status(thm)],[c_24,c_30]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_369,plain,
% 7.12/1.48      ( r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4))
% 7.12/1.48      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
% 7.12/1.48      | ~ v1_relat_1(sK4) ),
% 7.12/1.48      inference(unflattening,[status(thm)],[c_368]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_425,plain,
% 7.12/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
% 7.12/1.48      | ~ r1_tarski(X1,X2)
% 7.12/1.48      | ~ v1_relat_1(sK4)
% 7.12/1.48      | sK0(k1_relat_1(sK4),X0,sK4) != X2
% 7.12/1.48      | k1_relat_1(sK4) != X1 ),
% 7.12/1.48      inference(resolution_lifted,[status(thm)],[c_17,c_369]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_426,plain,
% 7.12/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
% 7.12/1.48      | ~ r1_tarski(k1_relat_1(sK4),sK0(k1_relat_1(sK4),X0,sK4))
% 7.12/1.48      | ~ v1_relat_1(sK4) ),
% 7.12/1.48      inference(unflattening,[status(thm)],[c_425]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_1352,plain,
% 7.12/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
% 7.12/1.48      | r1_tarski(k1_relat_1(sK4),sK0(k1_relat_1(sK4),X0,sK4)) != iProver_top
% 7.12/1.48      | v1_relat_1(sK4) != iProver_top ),
% 7.12/1.48      inference(predicate_to_equality,[status(thm)],[c_426]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_32,plain,
% 7.12/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) = iProver_top ),
% 7.12/1.48      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_427,plain,
% 7.12/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
% 7.12/1.48      | r1_tarski(k1_relat_1(sK4),sK0(k1_relat_1(sK4),X0,sK4)) != iProver_top
% 7.12/1.48      | v1_relat_1(sK4) != iProver_top ),
% 7.12/1.48      inference(predicate_to_equality,[status(thm)],[c_426]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_1510,plain,
% 7.12/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) != iProver_top
% 7.12/1.48      | v1_relat_1(sK4) = iProver_top ),
% 7.12/1.48      inference(predicate_to_equality,[status(thm)],[c_1509]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_1656,plain,
% 7.12/1.48      ( r1_tarski(k1_relat_1(sK4),sK0(k1_relat_1(sK4),X0,sK4)) != iProver_top
% 7.12/1.48      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top ),
% 7.12/1.48      inference(global_propositional_subsumption,
% 7.12/1.48                [status(thm)],
% 7.12/1.48                [c_1352,c_32,c_427,c_1510]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_1657,plain,
% 7.12/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
% 7.12/1.48      | r1_tarski(k1_relat_1(sK4),sK0(k1_relat_1(sK4),X0,sK4)) != iProver_top ),
% 7.12/1.48      inference(renaming,[status(thm)],[c_1656]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_4022,plain,
% 7.12/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) = iProver_top
% 7.12/1.48      | r1_tarski(k1_xboole_0,sK0(k1_xboole_0,X0,sK4)) != iProver_top ),
% 7.12/1.48      inference(demodulation,[status(thm)],[c_4002,c_1657]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_7,plain,
% 7.12/1.48      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.12/1.48      inference(cnf_transformation,[],[f100]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_4024,plain,
% 7.12/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 7.12/1.48      | r1_tarski(k1_xboole_0,sK0(k1_xboole_0,X0,sK4)) != iProver_top ),
% 7.12/1.48      inference(light_normalisation,[status(thm)],[c_4022,c_7]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_4500,plain,
% 7.12/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 7.12/1.48      inference(superposition,[status(thm)],[c_2388,c_4024]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_6598,plain,
% 7.12/1.48      ( r1_tarski(sK4,k1_xboole_0) = iProver_top ),
% 7.12/1.48      inference(superposition,[status(thm)],[c_4500,c_1362]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_1369,plain,
% 7.12/1.48      ( X0 = X1
% 7.12/1.48      | r1_tarski(X1,X0) != iProver_top
% 7.12/1.48      | r1_tarski(X0,X1) != iProver_top ),
% 7.12/1.48      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_8013,plain,
% 7.12/1.48      ( sK4 = k1_xboole_0 | r1_tarski(k1_xboole_0,sK4) != iProver_top ),
% 7.12/1.48      inference(superposition,[status(thm)],[c_6598,c_1369]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_2420,plain,
% 7.12/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4)) | r1_tarski(X0,sK4) ),
% 7.12/1.48      inference(instantiation,[status(thm)],[c_11]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_3461,plain,
% 7.12/1.48      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4))
% 7.12/1.48      | r1_tarski(k1_xboole_0,sK4) ),
% 7.12/1.48      inference(instantiation,[status(thm)],[c_2420]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_3462,plain,
% 7.12/1.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) != iProver_top
% 7.12/1.48      | r1_tarski(k1_xboole_0,sK4) = iProver_top ),
% 7.12/1.48      inference(predicate_to_equality,[status(thm)],[c_3461]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_3850,plain,
% 7.12/1.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) ),
% 7.12/1.48      inference(instantiation,[status(thm)],[c_9]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_3851,plain,
% 7.12/1.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) = iProver_top ),
% 7.12/1.48      inference(predicate_to_equality,[status(thm)],[c_3850]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_8949,plain,
% 7.12/1.48      ( sK4 = k1_xboole_0 ),
% 7.12/1.48      inference(global_propositional_subsumption,
% 7.12/1.48                [status(thm)],
% 7.12/1.48                [c_8013,c_3462,c_3851]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_21,plain,
% 7.12/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.12/1.48      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.12/1.48      inference(cnf_transformation,[],[f77]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_1358,plain,
% 7.12/1.48      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.12/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.12/1.48      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_3146,plain,
% 7.12/1.48      ( k2_relset_1(k1_xboole_0,X0,X1) = k2_relat_1(X1)
% 7.12/1.48      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.12/1.48      inference(superposition,[status(thm)],[c_7,c_1358]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_6607,plain,
% 7.12/1.48      ( k2_relset_1(k1_xboole_0,X0,sK4) = k2_relat_1(sK4) ),
% 7.12/1.48      inference(superposition,[status(thm)],[c_4500,c_3146]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_20,plain,
% 7.12/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.12/1.48      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 7.12/1.48      inference(cnf_transformation,[],[f76]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_1359,plain,
% 7.12/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.12/1.49      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 7.12/1.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_8017,plain,
% 7.12/1.49      ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(X0)) = iProver_top
% 7.12/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 7.12/1.49      inference(superposition,[status(thm)],[c_6607,c_1359]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_8024,plain,
% 7.12/1.49      ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(X0)) = iProver_top
% 7.12/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.12/1.49      inference(light_normalisation,[status(thm)],[c_8017,c_7]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_8312,plain,
% 7.12/1.49      ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(X0)) = iProver_top ),
% 7.12/1.49      inference(global_propositional_subsumption,[status(thm)],[c_8024,c_4500]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_8956,plain,
% 7.12/1.49      ( m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top ),
% 7.12/1.49      inference(demodulation,[status(thm)],[c_8949,c_8312]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_3781,plain,
% 7.12/1.49      ( k2_relset_1(k1_xboole_0,X0,k2_relset_1(X1,k1_xboole_0,X2)) = k2_relat_1(k2_relset_1(X1,k1_xboole_0,X2))
% 7.12/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top ),
% 7.12/1.49      inference(superposition,[status(thm)],[c_1359,c_3146]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_6,plain,
% 7.12/1.49      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.12/1.49      inference(cnf_transformation,[],[f99]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_3783,plain,
% 7.12/1.49      ( k2_relset_1(k1_xboole_0,X0,k2_relset_1(X1,k1_xboole_0,X2)) = k2_relat_1(k2_relset_1(X1,k1_xboole_0,X2))
% 7.12/1.49      | m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.12/1.49      inference(demodulation,[status(thm)],[c_3781,c_6]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_6603,plain,
% 7.12/1.49      ( k2_relset_1(k1_xboole_0,X0,k2_relset_1(X1,k1_xboole_0,sK4)) = k2_relat_1(k2_relset_1(X1,k1_xboole_0,sK4)) ),
% 7.12/1.49      inference(superposition,[status(thm)],[c_4500,c_3783]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_3145,plain,
% 7.12/1.49      ( k2_relset_1(X0,k1_xboole_0,X1) = k2_relat_1(X1)
% 7.12/1.49      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.12/1.49      inference(superposition,[status(thm)],[c_6,c_1358]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_6608,plain,
% 7.12/1.49      ( k2_relset_1(X0,k1_xboole_0,sK4) = k2_relat_1(sK4) ),
% 7.12/1.49      inference(superposition,[status(thm)],[c_4500,c_3145]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_6619,plain,
% 7.12/1.49      ( k2_relset_1(k1_xboole_0,X0,k2_relat_1(sK4)) = k2_relat_1(k2_relat_1(sK4)) ),
% 7.12/1.49      inference(demodulation,[status(thm)],[c_6603,c_6608]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_8862,plain,
% 7.12/1.49      ( m1_subset_1(k2_relat_1(k2_relat_1(sK4)),k1_zfmisc_1(X0)) = iProver_top
% 7.12/1.49      | m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 7.12/1.49      inference(superposition,[status(thm)],[c_6619,c_1359]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_8869,plain,
% 7.12/1.49      ( m1_subset_1(k2_relat_1(k2_relat_1(sK4)),k1_zfmisc_1(X0)) = iProver_top
% 7.12/1.49      | m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.12/1.49      inference(light_normalisation,[status(thm)],[c_8862,c_7]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_9375,plain,
% 7.12/1.49      ( m1_subset_1(k2_relat_1(k2_relat_1(k1_xboole_0)),k1_zfmisc_1(X0)) = iProver_top
% 7.12/1.49      | m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.12/1.49      inference(light_normalisation,[status(thm)],[c_8869,c_8949]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_2496,plain,
% 7.12/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.12/1.49      | r1_tarski(k2_relset_1(X1,X2,X0),X2) = iProver_top ),
% 7.12/1.49      inference(superposition,[status(thm)],[c_1359,c_1362]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_9382,plain,
% 7.12/1.49      ( m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.12/1.49      | r1_tarski(k2_relset_1(X0,X1,k2_relat_1(k2_relat_1(k1_xboole_0))),X1) = iProver_top ),
% 7.12/1.49      inference(superposition,[status(thm)],[c_9375,c_2496]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_3139,plain,
% 7.12/1.49      ( k2_relset_1(X0,X1,k2_relset_1(X2,k2_zfmisc_1(X0,X1),X3)) = k2_relat_1(k2_relset_1(X2,k2_zfmisc_1(X0,X1),X3))
% 7.12/1.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,k2_zfmisc_1(X0,X1)))) != iProver_top ),
% 7.12/1.49      inference(superposition,[status(thm)],[c_1359,c_1358]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_11876,plain,
% 7.12/1.49      ( k2_relset_1(X0,X1,k2_relset_1(X2,k2_zfmisc_1(X0,X1),k2_relat_1(k1_xboole_0))) = k2_relat_1(k2_relset_1(X2,k2_zfmisc_1(X0,X1),k2_relat_1(k1_xboole_0))) ),
% 7.12/1.49      inference(superposition,[status(thm)],[c_8956,c_3139]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_11471,plain,
% 7.12/1.49      ( k2_relset_1(X0,X1,k2_relset_1(X2,k2_zfmisc_1(X0,X1),k1_xboole_0)) = k2_relat_1(k2_relset_1(X2,k2_zfmisc_1(X0,X1),k1_xboole_0)) ),
% 7.12/1.49      inference(superposition,[status(thm)],[c_1364,c_3139]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_3137,plain,
% 7.12/1.49      ( k2_relset_1(X0,X1,k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
% 7.12/1.49      inference(superposition,[status(thm)],[c_1364,c_1358]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_11480,plain,
% 7.12/1.49      ( k2_relset_1(X0,X1,k2_relat_1(k1_xboole_0)) = k2_relat_1(k2_relat_1(k1_xboole_0)) ),
% 7.12/1.49      inference(demodulation,[status(thm)],[c_11471,c_3137]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_11941,plain,
% 7.12/1.49      ( k2_relset_1(X0,X1,k2_relat_1(k2_relat_1(k1_xboole_0))) = k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0))) ),
% 7.12/1.49      inference(demodulation,[status(thm)],[c_11876,c_11480]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_13899,plain,
% 7.12/1.49      ( m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.12/1.49      | r1_tarski(k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0))),X0) = iProver_top ),
% 7.12/1.49      inference(light_normalisation,[status(thm)],[c_9382,c_11941]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_13903,plain,
% 7.12/1.49      ( k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0))) = X0
% 7.12/1.49      | m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.12/1.49      | r1_tarski(X0,k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0)))) != iProver_top ),
% 7.12/1.49      inference(superposition,[status(thm)],[c_13899,c_1369]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_3674,plain,
% 7.12/1.49      ( k2_relset_1(X0,k1_xboole_0,k2_relset_1(X1,k1_xboole_0,X2)) = k2_relat_1(k2_relset_1(X1,k1_xboole_0,X2))
% 7.12/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top ),
% 7.12/1.49      inference(superposition,[status(thm)],[c_1359,c_3145]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_3676,plain,
% 7.12/1.49      ( k2_relset_1(X0,k1_xboole_0,k2_relset_1(X1,k1_xboole_0,X2)) = k2_relat_1(k2_relset_1(X1,k1_xboole_0,X2))
% 7.12/1.49      | m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.12/1.49      inference(demodulation,[status(thm)],[c_3674,c_6]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_6604,plain,
% 7.12/1.49      ( k2_relset_1(X0,k1_xboole_0,k2_relset_1(X1,k1_xboole_0,sK4)) = k2_relat_1(k2_relset_1(X1,k1_xboole_0,sK4)) ),
% 7.12/1.49      inference(superposition,[status(thm)],[c_4500,c_3676]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_6615,plain,
% 7.12/1.49      ( k2_relset_1(X0,k1_xboole_0,k2_relat_1(sK4)) = k2_relat_1(k2_relat_1(sK4)) ),
% 7.12/1.49      inference(demodulation,[status(thm)],[c_6604,c_6608]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_8851,plain,
% 7.12/1.49      ( m1_subset_1(k2_relat_1(k2_relat_1(sK4)),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 7.12/1.49      | m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) != iProver_top ),
% 7.12/1.49      inference(superposition,[status(thm)],[c_6615,c_1359]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_8856,plain,
% 7.12/1.49      ( m1_subset_1(k2_relat_1(k2_relat_1(sK4)),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 7.12/1.49      | m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.12/1.49      inference(light_normalisation,[status(thm)],[c_8851,c_6]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_9292,plain,
% 7.12/1.49      ( m1_subset_1(k2_relat_1(k2_relat_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 7.12/1.49      | m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.12/1.49      inference(light_normalisation,[status(thm)],[c_8856,c_8949]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_9294,plain,
% 7.12/1.49      ( m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.12/1.49      | r1_tarski(k2_relat_1(k2_relat_1(k1_xboole_0)),k1_xboole_0) = iProver_top ),
% 7.12/1.49      inference(superposition,[status(thm)],[c_9292,c_1362]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_13414,plain,
% 7.12/1.49      ( r1_tarski(k2_relat_1(k2_relat_1(k1_xboole_0)),k1_xboole_0) = iProver_top ),
% 7.12/1.49      inference(superposition,[status(thm)],[c_8956,c_9294]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_13417,plain,
% 7.12/1.49      ( k2_relat_1(k2_relat_1(k1_xboole_0)) = k1_xboole_0
% 7.12/1.49      | r1_tarski(k1_xboole_0,k2_relat_1(k2_relat_1(k1_xboole_0))) != iProver_top ),
% 7.12/1.49      inference(superposition,[status(thm)],[c_13414,c_1369]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_15561,plain,
% 7.12/1.49      ( k2_relat_1(k2_relat_1(k1_xboole_0)) = k1_xboole_0 ),
% 7.12/1.49      inference(superposition,[status(thm)],[c_2388,c_13417]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_22707,plain,
% 7.12/1.49      ( k2_relat_1(k1_xboole_0) = X0
% 7.12/1.49      | m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.12/1.49      | r1_tarski(X0,k2_relat_1(k1_xboole_0)) != iProver_top ),
% 7.12/1.49      inference(light_normalisation,[status(thm)],[c_13903,c_15561]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_22712,plain,
% 7.12/1.49      ( k2_relat_1(k1_xboole_0) = X0
% 7.12/1.49      | r1_tarski(X0,k2_relat_1(k1_xboole_0)) != iProver_top ),
% 7.12/1.49      inference(superposition,[status(thm)],[c_8956,c_22707]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_22719,plain,
% 7.12/1.49      ( k9_relat_1(k1_xboole_0,X0) = k2_relat_1(k1_xboole_0)
% 7.12/1.49      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.12/1.49      inference(superposition,[status(thm)],[c_1361,c_22712]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_22720,plain,
% 7.12/1.49      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.12/1.49      inference(superposition,[status(thm)],[c_2388,c_22712]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_22819,plain,
% 7.12/1.49      ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0
% 7.12/1.49      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.12/1.49      inference(light_normalisation,[status(thm)],[c_22719,c_22720]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_1602,plain,
% 7.12/1.49      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.12/1.49      | v1_relat_1(k1_xboole_0) ),
% 7.12/1.49      inference(instantiation,[status(thm)],[c_18]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_1603,plain,
% 7.12/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.12/1.49      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 7.12/1.49      inference(predicate_to_equality,[status(thm)],[c_1602]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_2183,plain,
% 7.12/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 7.12/1.49      inference(instantiation,[status(thm)],[c_9]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_2184,plain,
% 7.12/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
% 7.12/1.49      inference(predicate_to_equality,[status(thm)],[c_2183]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_23099,plain,
% 7.12/1.49      ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.12/1.49      inference(global_propositional_subsumption,
% 7.12/1.49                [status(thm)],
% 7.12/1.49                [c_22819,c_1603,c_2184]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_1357,plain,
% 7.12/1.49      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 7.12/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.12/1.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_4506,plain,
% 7.12/1.49      ( k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,X0) = k9_relat_1(sK4,X0) ),
% 7.12/1.49      inference(superposition,[status(thm)],[c_1355,c_1357]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_1356,plain,
% 7.12/1.49      ( r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
% 7.12/1.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_4636,plain,
% 7.12/1.49      ( r1_tarski(k9_relat_1(sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
% 7.12/1.49      inference(demodulation,[status(thm)],[c_4506,c_1356]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_8960,plain,
% 7.12/1.49      ( r1_tarski(k9_relat_1(k1_xboole_0,sK3),k2_enumset1(k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1))) != iProver_top ),
% 7.12/1.49      inference(demodulation,[status(thm)],[c_8949,c_4636]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_23103,plain,
% 7.12/1.49      ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1))) != iProver_top ),
% 7.12/1.49      inference(demodulation,[status(thm)],[c_23099,c_8960]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_23666,plain,
% 7.12/1.49      ( $false ),
% 7.12/1.49      inference(superposition,[status(thm)],[c_2388,c_23103]) ).
% 7.12/1.49  
% 7.12/1.49  
% 7.12/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.12/1.49  
% 7.12/1.49  ------                               Statistics
% 7.12/1.49  
% 7.12/1.49  ------ General
% 7.12/1.49  
% 7.12/1.49  abstr_ref_over_cycles:                  0
% 7.12/1.49  abstr_ref_under_cycles:                 0
% 7.12/1.49  gc_basic_clause_elim:                   0
% 7.12/1.49  forced_gc_time:                         0
% 7.12/1.49  parsing_time:                           0.008
% 7.12/1.49  unif_index_cands_time:                  0.
% 7.12/1.49  unif_index_add_time:                    0.
% 7.12/1.49  orderings_time:                         0.
% 7.12/1.49  out_proof_time:                         0.013
% 7.12/1.49  total_time:                             0.652
% 7.12/1.49  num_of_symbols:                         53
% 7.12/1.49  num_of_terms:                           24281
% 7.12/1.49  
% 7.12/1.49  ------ Preprocessing
% 7.12/1.49  
% 7.12/1.49  num_of_splits:                          1
% 7.12/1.49  num_of_split_atoms:                     1
% 7.12/1.49  num_of_reused_defs:                     0
% 7.12/1.49  num_eq_ax_congr_red:                    22
% 7.12/1.49  num_of_sem_filtered_clauses:            1
% 7.12/1.49  num_of_subtypes:                        0
% 7.12/1.49  monotx_restored_types:                  0
% 7.12/1.49  sat_num_of_epr_types:                   0
% 7.12/1.49  sat_num_of_non_cyclic_types:            0
% 7.12/1.49  sat_guarded_non_collapsed_types:        0
% 7.12/1.49  num_pure_diseq_elim:                    0
% 7.12/1.49  simp_replaced_by:                       0
% 7.12/1.49  res_preprocessed:                       129
% 7.12/1.49  prep_upred:                             0
% 7.12/1.49  prep_unflattend:                        16
% 7.12/1.49  smt_new_axioms:                         0
% 7.12/1.49  pred_elim_cands:                        3
% 7.12/1.49  pred_elim:                              3
% 7.12/1.49  pred_elim_cl:                           4
% 7.12/1.49  pred_elim_cycles:                       5
% 7.12/1.49  merged_defs:                            8
% 7.12/1.49  merged_defs_ncl:                        0
% 7.12/1.49  bin_hyper_res:                          8
% 7.12/1.49  prep_cycles:                            4
% 7.12/1.49  pred_elim_time:                         0.005
% 7.12/1.49  splitting_time:                         0.
% 7.12/1.49  sem_filter_time:                        0.
% 7.12/1.49  monotx_time:                            0.
% 7.12/1.49  subtype_inf_time:                       0.
% 7.12/1.49  
% 7.12/1.49  ------ Problem properties
% 7.12/1.49  
% 7.12/1.49  clauses:                                25
% 7.12/1.49  conjectures:                            3
% 7.12/1.49  epr:                                    3
% 7.12/1.49  horn:                                   21
% 7.12/1.49  ground:                                 4
% 7.12/1.49  unary:                                  9
% 7.12/1.49  binary:                                 8
% 7.12/1.49  lits:                                   50
% 7.12/1.49  lits_eq:                                14
% 7.12/1.49  fd_pure:                                0
% 7.12/1.49  fd_pseudo:                              0
% 7.12/1.49  fd_cond:                                1
% 7.12/1.49  fd_pseudo_cond:                         2
% 7.12/1.49  ac_symbols:                             0
% 7.12/1.49  
% 7.12/1.49  ------ Propositional Solver
% 7.12/1.49  
% 7.12/1.49  prop_solver_calls:                      32
% 7.12/1.49  prop_fast_solver_calls:                 1495
% 7.12/1.49  smt_solver_calls:                       0
% 7.12/1.49  smt_fast_solver_calls:                  0
% 7.12/1.49  prop_num_of_clauses:                    10677
% 7.12/1.49  prop_preprocess_simplified:             16890
% 7.12/1.49  prop_fo_subsumed:                       68
% 7.12/1.49  prop_solver_time:                       0.
% 7.12/1.49  smt_solver_time:                        0.
% 7.12/1.49  smt_fast_solver_time:                   0.
% 7.12/1.49  prop_fast_solver_time:                  0.
% 7.12/1.49  prop_unsat_core_time:                   0.
% 7.12/1.49  
% 7.12/1.49  ------ QBF
% 7.12/1.49  
% 7.12/1.49  qbf_q_res:                              0
% 7.12/1.49  qbf_num_tautologies:                    0
% 7.12/1.49  qbf_prep_cycles:                        0
% 7.12/1.49  
% 7.12/1.49  ------ BMC1
% 7.12/1.49  
% 7.12/1.49  bmc1_current_bound:                     -1
% 7.12/1.49  bmc1_last_solved_bound:                 -1
% 7.12/1.49  bmc1_unsat_core_size:                   -1
% 7.12/1.49  bmc1_unsat_core_parents_size:           -1
% 7.12/1.49  bmc1_merge_next_fun:                    0
% 7.12/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.12/1.49  
% 7.12/1.49  ------ Instantiation
% 7.12/1.49  
% 7.12/1.49  inst_num_of_clauses:                    2630
% 7.12/1.49  inst_num_in_passive:                    235
% 7.12/1.49  inst_num_in_active:                     1179
% 7.12/1.49  inst_num_in_unprocessed:                1216
% 7.12/1.49  inst_num_of_loops:                      1270
% 7.12/1.49  inst_num_of_learning_restarts:          0
% 7.12/1.49  inst_num_moves_active_passive:          87
% 7.12/1.49  inst_lit_activity:                      0
% 7.12/1.49  inst_lit_activity_moves:                0
% 7.12/1.49  inst_num_tautologies:                   0
% 7.12/1.49  inst_num_prop_implied:                  0
% 7.12/1.49  inst_num_existing_simplified:           0
% 7.12/1.49  inst_num_eq_res_simplified:             0
% 7.12/1.49  inst_num_child_elim:                    0
% 7.12/1.49  inst_num_of_dismatching_blockings:      2291
% 7.12/1.49  inst_num_of_non_proper_insts:           4030
% 7.12/1.49  inst_num_of_duplicates:                 0
% 7.12/1.49  inst_inst_num_from_inst_to_res:         0
% 7.12/1.49  inst_dismatching_checking_time:         0.
% 7.12/1.49  
% 7.12/1.49  ------ Resolution
% 7.12/1.49  
% 7.12/1.49  res_num_of_clauses:                     0
% 7.12/1.49  res_num_in_passive:                     0
% 7.12/1.49  res_num_in_active:                      0
% 7.12/1.49  res_num_of_loops:                       133
% 7.12/1.49  res_forward_subset_subsumed:            471
% 7.12/1.49  res_backward_subset_subsumed:           4
% 7.12/1.49  res_forward_subsumed:                   0
% 7.12/1.49  res_backward_subsumed:                  0
% 7.12/1.49  res_forward_subsumption_resolution:     0
% 7.12/1.49  res_backward_subsumption_resolution:    0
% 7.12/1.49  res_clause_to_clause_subsumption:       5498
% 7.12/1.49  res_orphan_elimination:                 0
% 7.12/1.49  res_tautology_del:                      324
% 7.12/1.49  res_num_eq_res_simplified:              0
% 7.12/1.49  res_num_sel_changes:                    0
% 7.12/1.49  res_moves_from_active_to_pass:          0
% 7.12/1.49  
% 7.12/1.49  ------ Superposition
% 7.12/1.49  
% 7.12/1.49  sup_time_total:                         0.
% 7.12/1.49  sup_time_generating:                    0.
% 7.12/1.49  sup_time_sim_full:                      0.
% 7.12/1.49  sup_time_sim_immed:                     0.
% 7.12/1.49  
% 7.12/1.49  sup_num_of_clauses:                     527
% 7.12/1.49  sup_num_in_active:                      161
% 7.12/1.49  sup_num_in_passive:                     366
% 7.12/1.49  sup_num_of_loops:                       252
% 7.12/1.49  sup_fw_superposition:                   768
% 7.12/1.49  sup_bw_superposition:                   349
% 7.12/1.49  sup_immediate_simplified:               632
% 7.12/1.49  sup_given_eliminated:                   8
% 7.12/1.49  comparisons_done:                       0
% 7.12/1.49  comparisons_avoided:                    8
% 7.12/1.49  
% 7.12/1.49  ------ Simplifications
% 7.12/1.49  
% 7.12/1.49  
% 7.12/1.49  sim_fw_subset_subsumed:                 33
% 7.12/1.49  sim_bw_subset_subsumed:                 61
% 7.12/1.49  sim_fw_subsumed:                        59
% 7.12/1.49  sim_bw_subsumed:                        24
% 7.12/1.49  sim_fw_subsumption_res:                 0
% 7.12/1.49  sim_bw_subsumption_res:                 0
% 7.12/1.49  sim_tautology_del:                      1
% 7.12/1.49  sim_eq_tautology_del:                   254
% 7.12/1.49  sim_eq_res_simp:                        0
% 7.12/1.49  sim_fw_demodulated:                     520
% 7.12/1.49  sim_bw_demodulated:                     95
% 7.12/1.49  sim_light_normalised:                   316
% 7.12/1.49  sim_joinable_taut:                      0
% 7.12/1.49  sim_joinable_simp:                      0
% 7.12/1.49  sim_ac_normalised:                      0
% 7.12/1.49  sim_smt_subsumption:                    0
% 7.12/1.49  
%------------------------------------------------------------------------------
