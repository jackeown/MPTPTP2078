%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:54 EST 2020

% Result     : Theorem 3.49s
% Output     : CNFRefutation 3.49s
% Verified   : 
% Statistics : Number of formulae       :  195 (4783 expanded)
%              Number of clauses        :  106 ( 982 expanded)
%              Number of leaves         :   24 (1207 expanded)
%              Depth                    :   32
%              Number of atoms          :  460 (9307 expanded)
%              Number of equality atoms :  244 (4498 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f25,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(pure_predicate_removal,[],[f24])).

fof(f42,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f43,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f42])).

fof(f50,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
        & k1_xboole_0 != X1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
      & k1_xboole_0 != sK1
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f43,f50])).

fof(f82,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f51])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f85,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f61,f62])).

fof(f86,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f60,f85])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f59,f86])).

fof(f88,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f58,f87])).

fof(f89,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f57,f88])).

fof(f90,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f56,f89])).

fof(f96,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f82,f90])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f46])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f93,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f63,f90,f90])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f13,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f44])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f98,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( r1_tarski(X0,X3)
       => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f40])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f54,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f94,plain,(
    ! [X0,X1] :
      ( k6_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f77,f90,f90])).

fof(f81,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f84,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f51])).

fof(f95,plain,(
    ~ r1_tarski(k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f84,f90,f90])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v4_relat_1(X1,X0)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f49,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f74,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_921,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_19,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_925,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1485,plain,
    ( v4_relat_1(sK3,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_921,c_925])).

cnf(c_9,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_934,plain,
    ( v4_relat_1(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_937,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2649,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_relat_1(X1)
    | k1_relat_1(X1) = k1_xboole_0
    | v4_relat_1(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_934,c_937])).

cnf(c_7932,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1485,c_2649])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_982,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0)
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1039,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_982])).

cnf(c_1151,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1039])).

cnf(c_10,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1185,plain,
    ( v1_relat_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_7940,plain,
    ( ~ v1_relat_1(sK3)
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7932])).

cnf(c_8135,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7932,c_24,c_1151,c_1185,c_7940])).

cnf(c_8136,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_8135])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_941,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_940,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X3,X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_923,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(X3,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1375,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_921,c_923])).

cnf(c_1621,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) = iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1375,c_923])).

cnf(c_1717,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_940,c_1621])).

cnf(c_1726,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_941,c_1717])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_924,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2168,plain,
    ( k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,k1_xboole_0,X0) = k9_relat_1(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_1726,c_924])).

cnf(c_17,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_926,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_942,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2037,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_940,c_942])).

cnf(c_3243,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_926,c_2037])).

cnf(c_1186,plain,
    ( v1_relat_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1185])).

cnf(c_1208,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2008,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))
    | v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1208])).

cnf(c_2009,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2008])).

cnf(c_3251,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3243,c_1186,c_1726,c_2009])).

cnf(c_936,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2154,plain,
    ( r1_tarski(X0,sK3) != iProver_top
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1375,c_936])).

cnf(c_2463,plain,
    ( v1_relat_1(X0) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2154,c_1186])).

cnf(c_2464,plain,
    ( r1_tarski(X0,sK3) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_2463])).

cnf(c_2470,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_940,c_2464])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_932,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2477,plain,
    ( k2_relat_1(k7_relat_1(k1_xboole_0,X0)) = k9_relat_1(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_2470,c_932])).

cnf(c_3254,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_3251,c_2477])).

cnf(c_4506,plain,
    ( k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,k1_xboole_0,X0) = k2_relat_1(k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_2168,c_2168,c_3254])).

cnf(c_8155,plain,
    ( k7_relset_1(k1_relat_1(sK3),sK1,k1_xboole_0,X0) = k2_relat_1(k1_xboole_0)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8136,c_4506])).

cnf(c_27,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1152,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1151])).

cnf(c_2153,plain,
    ( v1_relat_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_921,c_936])).

cnf(c_2238,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2153,c_27,c_1152,c_1186])).

cnf(c_2242,plain,
    ( k2_relat_1(k7_relat_1(sK3,X0)) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_2238,c_932])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_930,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2546,plain,
    ( r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(X1)) = iProver_top
    | r1_tarski(k7_relat_1(sK3,X0),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2242,c_930])).

cnf(c_2471,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_926,c_2464])).

cnf(c_3112,plain,
    ( v1_relat_1(X1) != iProver_top
    | r1_tarski(k7_relat_1(sK3,X0),X1) != iProver_top
    | r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(X1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2546,c_27,c_1152,c_1186,c_2471])).

cnf(c_3113,plain,
    ( r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(X1)) = iProver_top
    | r1_tarski(k7_relat_1(sK3,X0),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_3112])).

cnf(c_18,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k1_relat_1(X0)
    | k6_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_277,plain,
    ( ~ v1_relat_1(X0)
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k1_relat_1(X0)
    | k6_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_25])).

cnf(c_278,plain,
    ( ~ v1_relat_1(sK3)
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(sK3)
    | k6_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_277])).

cnf(c_920,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(sK3)
    | k6_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_278])).

cnf(c_8139,plain,
    ( k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_8136,c_920])).

cnf(c_8403,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8139,c_27,c_1152,c_1186])).

cnf(c_8404,plain,
    ( k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_8403])).

cnf(c_2166,plain,
    ( k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_921,c_924])).

cnf(c_22,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_922,plain,
    ( r1_tarski(k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2235,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2166,c_922])).

cnf(c_8408,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8404,c_2235])).

cnf(c_8418,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3113,c_8408])).

cnf(c_8915,plain,
    ( r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8418,c_27,c_1152,c_1186])).

cnf(c_8916,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_8915])).

cnf(c_8919,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_926,c_8916])).

cnf(c_9045,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8155,c_27,c_1152,c_1186,c_8919])).

cnf(c_8,plain,
    ( v4_relat_1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_935,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_9086,plain,
    ( v4_relat_1(sK3,X0) = iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_9045,c_935])).

cnf(c_79,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_9511,plain,
    ( v4_relat_1(sK3,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9086,c_27,c_79,c_1152,c_1186])).

cnf(c_12,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_931,plain,
    ( k7_relat_1(X0,X1) = X0
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_9518,plain,
    ( k7_relat_1(sK3,X0) = sK3
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_9511,c_931])).

cnf(c_2071,plain,
    ( ~ v4_relat_1(sK3,X0)
    | ~ v1_relat_1(sK3)
    | k7_relat_1(sK3,X0) = sK3 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2072,plain,
    ( k7_relat_1(sK3,X0) = sK3
    | v4_relat_1(sK3,X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2071])).

cnf(c_9535,plain,
    ( k7_relat_1(sK3,X0) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9518,c_27,c_79,c_1152,c_1186,c_2072,c_9086])).

cnf(c_9559,plain,
    ( k9_relat_1(sK3,X0) = k2_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_9535,c_2242])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_927,plain,
    ( k2_relat_1(X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_9089,plain,
    ( k2_relat_1(sK3) = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_9045,c_927])).

cnf(c_3104,plain,
    ( ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) = k1_xboole_0
    | k1_relat_1(sK3) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_9339,plain,
    ( k2_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9089,c_24,c_27,c_1151,c_1152,c_1185,c_1186,c_3104,c_8919])).

cnf(c_9562,plain,
    ( k9_relat_1(sK3,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_9559,c_9339])).

cnf(c_11248,plain,
    ( r1_tarski(k1_xboole_0,k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9562,c_2235])).

cnf(c_4550,plain,
    ( r1_tarski(k1_xboole_0,k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4551,plain,
    ( r1_tarski(k1_xboole_0,k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4550])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11248,c_4551])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:23:01 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.49/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.49/0.99  
% 3.49/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.49/0.99  
% 3.49/0.99  ------  iProver source info
% 3.49/0.99  
% 3.49/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.49/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.49/0.99  git: non_committed_changes: false
% 3.49/0.99  git: last_make_outside_of_git: false
% 3.49/0.99  
% 3.49/0.99  ------ 
% 3.49/0.99  
% 3.49/0.99  ------ Input Options
% 3.49/0.99  
% 3.49/0.99  --out_options                           all
% 3.49/0.99  --tptp_safe_out                         true
% 3.49/0.99  --problem_path                          ""
% 3.49/0.99  --include_path                          ""
% 3.49/0.99  --clausifier                            res/vclausify_rel
% 3.49/0.99  --clausifier_options                    ""
% 3.49/0.99  --stdin                                 false
% 3.49/0.99  --stats_out                             all
% 3.49/0.99  
% 3.49/0.99  ------ General Options
% 3.49/0.99  
% 3.49/0.99  --fof                                   false
% 3.49/0.99  --time_out_real                         305.
% 3.49/0.99  --time_out_virtual                      -1.
% 3.49/0.99  --symbol_type_check                     false
% 3.49/0.99  --clausify_out                          false
% 3.49/0.99  --sig_cnt_out                           false
% 3.49/0.99  --trig_cnt_out                          false
% 3.49/0.99  --trig_cnt_out_tolerance                1.
% 3.49/0.99  --trig_cnt_out_sk_spl                   false
% 3.49/0.99  --abstr_cl_out                          false
% 3.49/0.99  
% 3.49/0.99  ------ Global Options
% 3.49/0.99  
% 3.49/0.99  --schedule                              default
% 3.49/0.99  --add_important_lit                     false
% 3.49/0.99  --prop_solver_per_cl                    1000
% 3.49/0.99  --min_unsat_core                        false
% 3.49/0.99  --soft_assumptions                      false
% 3.49/0.99  --soft_lemma_size                       3
% 3.49/0.99  --prop_impl_unit_size                   0
% 3.49/0.99  --prop_impl_unit                        []
% 3.49/0.99  --share_sel_clauses                     true
% 3.49/0.99  --reset_solvers                         false
% 3.49/0.99  --bc_imp_inh                            [conj_cone]
% 3.49/0.99  --conj_cone_tolerance                   3.
% 3.49/0.99  --extra_neg_conj                        none
% 3.49/0.99  --large_theory_mode                     true
% 3.49/0.99  --prolific_symb_bound                   200
% 3.49/0.99  --lt_threshold                          2000
% 3.49/0.99  --clause_weak_htbl                      true
% 3.49/0.99  --gc_record_bc_elim                     false
% 3.49/0.99  
% 3.49/0.99  ------ Preprocessing Options
% 3.49/0.99  
% 3.49/0.99  --preprocessing_flag                    true
% 3.49/0.99  --time_out_prep_mult                    0.1
% 3.49/0.99  --splitting_mode                        input
% 3.49/0.99  --splitting_grd                         true
% 3.49/0.99  --splitting_cvd                         false
% 3.49/0.99  --splitting_cvd_svl                     false
% 3.49/0.99  --splitting_nvd                         32
% 3.49/0.99  --sub_typing                            true
% 3.49/0.99  --prep_gs_sim                           true
% 3.49/0.99  --prep_unflatten                        true
% 3.49/0.99  --prep_res_sim                          true
% 3.49/0.99  --prep_upred                            true
% 3.49/0.99  --prep_sem_filter                       exhaustive
% 3.49/0.99  --prep_sem_filter_out                   false
% 3.49/0.99  --pred_elim                             true
% 3.49/0.99  --res_sim_input                         true
% 3.49/0.99  --eq_ax_congr_red                       true
% 3.49/0.99  --pure_diseq_elim                       true
% 3.49/0.99  --brand_transform                       false
% 3.49/0.99  --non_eq_to_eq                          false
% 3.49/0.99  --prep_def_merge                        true
% 3.49/0.99  --prep_def_merge_prop_impl              false
% 3.49/0.99  --prep_def_merge_mbd                    true
% 3.49/0.99  --prep_def_merge_tr_red                 false
% 3.49/0.99  --prep_def_merge_tr_cl                  false
% 3.49/0.99  --smt_preprocessing                     true
% 3.49/0.99  --smt_ac_axioms                         fast
% 3.49/0.99  --preprocessed_out                      false
% 3.49/0.99  --preprocessed_stats                    false
% 3.49/0.99  
% 3.49/0.99  ------ Abstraction refinement Options
% 3.49/0.99  
% 3.49/0.99  --abstr_ref                             []
% 3.49/0.99  --abstr_ref_prep                        false
% 3.49/0.99  --abstr_ref_until_sat                   false
% 3.49/0.99  --abstr_ref_sig_restrict                funpre
% 3.49/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.49/0.99  --abstr_ref_under                       []
% 3.49/0.99  
% 3.49/0.99  ------ SAT Options
% 3.49/0.99  
% 3.49/0.99  --sat_mode                              false
% 3.49/0.99  --sat_fm_restart_options                ""
% 3.49/0.99  --sat_gr_def                            false
% 3.49/0.99  --sat_epr_types                         true
% 3.49/0.99  --sat_non_cyclic_types                  false
% 3.49/0.99  --sat_finite_models                     false
% 3.49/0.99  --sat_fm_lemmas                         false
% 3.49/0.99  --sat_fm_prep                           false
% 3.49/0.99  --sat_fm_uc_incr                        true
% 3.49/0.99  --sat_out_model                         small
% 3.49/0.99  --sat_out_clauses                       false
% 3.49/0.99  
% 3.49/0.99  ------ QBF Options
% 3.49/0.99  
% 3.49/0.99  --qbf_mode                              false
% 3.49/0.99  --qbf_elim_univ                         false
% 3.49/0.99  --qbf_dom_inst                          none
% 3.49/0.99  --qbf_dom_pre_inst                      false
% 3.49/0.99  --qbf_sk_in                             false
% 3.49/0.99  --qbf_pred_elim                         true
% 3.49/0.99  --qbf_split                             512
% 3.49/0.99  
% 3.49/0.99  ------ BMC1 Options
% 3.49/0.99  
% 3.49/0.99  --bmc1_incremental                      false
% 3.49/0.99  --bmc1_axioms                           reachable_all
% 3.49/0.99  --bmc1_min_bound                        0
% 3.49/0.99  --bmc1_max_bound                        -1
% 3.49/0.99  --bmc1_max_bound_default                -1
% 3.49/0.99  --bmc1_symbol_reachability              true
% 3.49/0.99  --bmc1_property_lemmas                  false
% 3.49/0.99  --bmc1_k_induction                      false
% 3.49/0.99  --bmc1_non_equiv_states                 false
% 3.49/0.99  --bmc1_deadlock                         false
% 3.49/0.99  --bmc1_ucm                              false
% 3.49/0.99  --bmc1_add_unsat_core                   none
% 3.49/0.99  --bmc1_unsat_core_children              false
% 3.49/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.49/0.99  --bmc1_out_stat                         full
% 3.49/0.99  --bmc1_ground_init                      false
% 3.49/0.99  --bmc1_pre_inst_next_state              false
% 3.49/0.99  --bmc1_pre_inst_state                   false
% 3.49/0.99  --bmc1_pre_inst_reach_state             false
% 3.49/0.99  --bmc1_out_unsat_core                   false
% 3.49/0.99  --bmc1_aig_witness_out                  false
% 3.49/0.99  --bmc1_verbose                          false
% 3.49/0.99  --bmc1_dump_clauses_tptp                false
% 3.49/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.49/0.99  --bmc1_dump_file                        -
% 3.49/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.49/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.49/0.99  --bmc1_ucm_extend_mode                  1
% 3.49/0.99  --bmc1_ucm_init_mode                    2
% 3.49/0.99  --bmc1_ucm_cone_mode                    none
% 3.49/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.49/0.99  --bmc1_ucm_relax_model                  4
% 3.49/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.49/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.49/0.99  --bmc1_ucm_layered_model                none
% 3.49/0.99  --bmc1_ucm_max_lemma_size               10
% 3.49/0.99  
% 3.49/0.99  ------ AIG Options
% 3.49/0.99  
% 3.49/0.99  --aig_mode                              false
% 3.49/0.99  
% 3.49/0.99  ------ Instantiation Options
% 3.49/0.99  
% 3.49/0.99  --instantiation_flag                    true
% 3.49/0.99  --inst_sos_flag                         true
% 3.49/0.99  --inst_sos_phase                        true
% 3.49/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.49/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.49/0.99  --inst_lit_sel_side                     num_symb
% 3.49/0.99  --inst_solver_per_active                1400
% 3.49/0.99  --inst_solver_calls_frac                1.
% 3.49/0.99  --inst_passive_queue_type               priority_queues
% 3.49/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.49/0.99  --inst_passive_queues_freq              [25;2]
% 3.49/0.99  --inst_dismatching                      true
% 3.49/0.99  --inst_eager_unprocessed_to_passive     true
% 3.49/0.99  --inst_prop_sim_given                   true
% 3.49/0.99  --inst_prop_sim_new                     false
% 3.49/0.99  --inst_subs_new                         false
% 3.49/0.99  --inst_eq_res_simp                      false
% 3.49/0.99  --inst_subs_given                       false
% 3.49/0.99  --inst_orphan_elimination               true
% 3.49/0.99  --inst_learning_loop_flag               true
% 3.49/0.99  --inst_learning_start                   3000
% 3.49/0.99  --inst_learning_factor                  2
% 3.49/0.99  --inst_start_prop_sim_after_learn       3
% 3.49/0.99  --inst_sel_renew                        solver
% 3.49/0.99  --inst_lit_activity_flag                true
% 3.49/0.99  --inst_restr_to_given                   false
% 3.49/0.99  --inst_activity_threshold               500
% 3.49/0.99  --inst_out_proof                        true
% 3.49/0.99  
% 3.49/0.99  ------ Resolution Options
% 3.49/0.99  
% 3.49/0.99  --resolution_flag                       true
% 3.49/0.99  --res_lit_sel                           adaptive
% 3.49/0.99  --res_lit_sel_side                      none
% 3.49/0.99  --res_ordering                          kbo
% 3.49/0.99  --res_to_prop_solver                    active
% 3.49/0.99  --res_prop_simpl_new                    false
% 3.49/0.99  --res_prop_simpl_given                  true
% 3.49/0.99  --res_passive_queue_type                priority_queues
% 3.49/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.49/0.99  --res_passive_queues_freq               [15;5]
% 3.49/0.99  --res_forward_subs                      full
% 3.49/0.99  --res_backward_subs                     full
% 3.49/0.99  --res_forward_subs_resolution           true
% 3.49/0.99  --res_backward_subs_resolution          true
% 3.49/0.99  --res_orphan_elimination                true
% 3.49/0.99  --res_time_limit                        2.
% 3.49/0.99  --res_out_proof                         true
% 3.49/0.99  
% 3.49/0.99  ------ Superposition Options
% 3.49/0.99  
% 3.49/0.99  --superposition_flag                    true
% 3.49/0.99  --sup_passive_queue_type                priority_queues
% 3.49/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.49/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.49/0.99  --demod_completeness_check              fast
% 3.49/0.99  --demod_use_ground                      true
% 3.49/0.99  --sup_to_prop_solver                    passive
% 3.49/0.99  --sup_prop_simpl_new                    true
% 3.49/0.99  --sup_prop_simpl_given                  true
% 3.49/0.99  --sup_fun_splitting                     true
% 3.49/0.99  --sup_smt_interval                      50000
% 3.49/0.99  
% 3.49/0.99  ------ Superposition Simplification Setup
% 3.49/0.99  
% 3.49/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.49/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.49/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.49/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.49/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.49/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.49/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.49/0.99  --sup_immed_triv                        [TrivRules]
% 3.49/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.49/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.49/0.99  --sup_immed_bw_main                     []
% 3.49/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.49/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.49/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.49/0.99  --sup_input_bw                          []
% 3.49/0.99  
% 3.49/0.99  ------ Combination Options
% 3.49/0.99  
% 3.49/0.99  --comb_res_mult                         3
% 3.49/0.99  --comb_sup_mult                         2
% 3.49/0.99  --comb_inst_mult                        10
% 3.49/0.99  
% 3.49/0.99  ------ Debug Options
% 3.49/0.99  
% 3.49/0.99  --dbg_backtrace                         false
% 3.49/0.99  --dbg_dump_prop_clauses                 false
% 3.49/0.99  --dbg_dump_prop_clauses_file            -
% 3.49/0.99  --dbg_out_stat                          false
% 3.49/0.99  ------ Parsing...
% 3.49/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.49/0.99  
% 3.49/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.49/0.99  
% 3.49/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.49/0.99  
% 3.49/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.49/0.99  ------ Proving...
% 3.49/0.99  ------ Problem Properties 
% 3.49/0.99  
% 3.49/0.99  
% 3.49/0.99  clauses                                 24
% 3.49/0.99  conjectures                             3
% 3.49/0.99  EPR                                     4
% 3.49/0.99  Horn                                    23
% 3.49/0.99  unary                                   8
% 3.49/0.99  binary                                  4
% 3.49/0.99  lits                                    54
% 3.49/0.99  lits eq                                 13
% 3.49/0.99  fd_pure                                 0
% 3.49/0.99  fd_pseudo                               0
% 3.49/0.99  fd_cond                                 0
% 3.49/0.99  fd_pseudo_cond                          2
% 3.49/0.99  AC symbols                              0
% 3.49/0.99  
% 3.49/0.99  ------ Schedule dynamic 5 is on 
% 3.49/0.99  
% 3.49/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.49/0.99  
% 3.49/0.99  
% 3.49/0.99  ------ 
% 3.49/0.99  Current options:
% 3.49/0.99  ------ 
% 3.49/0.99  
% 3.49/0.99  ------ Input Options
% 3.49/0.99  
% 3.49/0.99  --out_options                           all
% 3.49/0.99  --tptp_safe_out                         true
% 3.49/0.99  --problem_path                          ""
% 3.49/0.99  --include_path                          ""
% 3.49/0.99  --clausifier                            res/vclausify_rel
% 3.49/0.99  --clausifier_options                    ""
% 3.49/0.99  --stdin                                 false
% 3.49/0.99  --stats_out                             all
% 3.49/0.99  
% 3.49/0.99  ------ General Options
% 3.49/0.99  
% 3.49/0.99  --fof                                   false
% 3.49/0.99  --time_out_real                         305.
% 3.49/0.99  --time_out_virtual                      -1.
% 3.49/0.99  --symbol_type_check                     false
% 3.49/0.99  --clausify_out                          false
% 3.49/0.99  --sig_cnt_out                           false
% 3.49/0.99  --trig_cnt_out                          false
% 3.49/0.99  --trig_cnt_out_tolerance                1.
% 3.49/0.99  --trig_cnt_out_sk_spl                   false
% 3.49/0.99  --abstr_cl_out                          false
% 3.49/0.99  
% 3.49/0.99  ------ Global Options
% 3.49/0.99  
% 3.49/0.99  --schedule                              default
% 3.49/0.99  --add_important_lit                     false
% 3.49/0.99  --prop_solver_per_cl                    1000
% 3.49/0.99  --min_unsat_core                        false
% 3.49/0.99  --soft_assumptions                      false
% 3.49/0.99  --soft_lemma_size                       3
% 3.49/0.99  --prop_impl_unit_size                   0
% 3.49/0.99  --prop_impl_unit                        []
% 3.49/0.99  --share_sel_clauses                     true
% 3.49/0.99  --reset_solvers                         false
% 3.49/0.99  --bc_imp_inh                            [conj_cone]
% 3.49/0.99  --conj_cone_tolerance                   3.
% 3.49/0.99  --extra_neg_conj                        none
% 3.49/0.99  --large_theory_mode                     true
% 3.49/0.99  --prolific_symb_bound                   200
% 3.49/0.99  --lt_threshold                          2000
% 3.49/0.99  --clause_weak_htbl                      true
% 3.49/0.99  --gc_record_bc_elim                     false
% 3.49/0.99  
% 3.49/0.99  ------ Preprocessing Options
% 3.49/0.99  
% 3.49/0.99  --preprocessing_flag                    true
% 3.49/0.99  --time_out_prep_mult                    0.1
% 3.49/0.99  --splitting_mode                        input
% 3.49/0.99  --splitting_grd                         true
% 3.49/0.99  --splitting_cvd                         false
% 3.49/0.99  --splitting_cvd_svl                     false
% 3.49/0.99  --splitting_nvd                         32
% 3.49/0.99  --sub_typing                            true
% 3.49/0.99  --prep_gs_sim                           true
% 3.49/0.99  --prep_unflatten                        true
% 3.49/0.99  --prep_res_sim                          true
% 3.49/0.99  --prep_upred                            true
% 3.49/0.99  --prep_sem_filter                       exhaustive
% 3.49/0.99  --prep_sem_filter_out                   false
% 3.49/0.99  --pred_elim                             true
% 3.49/0.99  --res_sim_input                         true
% 3.49/0.99  --eq_ax_congr_red                       true
% 3.49/0.99  --pure_diseq_elim                       true
% 3.49/0.99  --brand_transform                       false
% 3.49/0.99  --non_eq_to_eq                          false
% 3.49/0.99  --prep_def_merge                        true
% 3.49/0.99  --prep_def_merge_prop_impl              false
% 3.49/0.99  --prep_def_merge_mbd                    true
% 3.49/0.99  --prep_def_merge_tr_red                 false
% 3.49/0.99  --prep_def_merge_tr_cl                  false
% 3.49/0.99  --smt_preprocessing                     true
% 3.49/0.99  --smt_ac_axioms                         fast
% 3.49/0.99  --preprocessed_out                      false
% 3.49/0.99  --preprocessed_stats                    false
% 3.49/0.99  
% 3.49/0.99  ------ Abstraction refinement Options
% 3.49/0.99  
% 3.49/0.99  --abstr_ref                             []
% 3.49/0.99  --abstr_ref_prep                        false
% 3.49/0.99  --abstr_ref_until_sat                   false
% 3.49/0.99  --abstr_ref_sig_restrict                funpre
% 3.49/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.49/0.99  --abstr_ref_under                       []
% 3.49/0.99  
% 3.49/0.99  ------ SAT Options
% 3.49/0.99  
% 3.49/0.99  --sat_mode                              false
% 3.49/0.99  --sat_fm_restart_options                ""
% 3.49/0.99  --sat_gr_def                            false
% 3.49/0.99  --sat_epr_types                         true
% 3.49/0.99  --sat_non_cyclic_types                  false
% 3.49/0.99  --sat_finite_models                     false
% 3.49/0.99  --sat_fm_lemmas                         false
% 3.49/0.99  --sat_fm_prep                           false
% 3.49/0.99  --sat_fm_uc_incr                        true
% 3.49/0.99  --sat_out_model                         small
% 3.49/0.99  --sat_out_clauses                       false
% 3.49/0.99  
% 3.49/0.99  ------ QBF Options
% 3.49/0.99  
% 3.49/0.99  --qbf_mode                              false
% 3.49/0.99  --qbf_elim_univ                         false
% 3.49/0.99  --qbf_dom_inst                          none
% 3.49/0.99  --qbf_dom_pre_inst                      false
% 3.49/0.99  --qbf_sk_in                             false
% 3.49/0.99  --qbf_pred_elim                         true
% 3.49/0.99  --qbf_split                             512
% 3.49/0.99  
% 3.49/0.99  ------ BMC1 Options
% 3.49/0.99  
% 3.49/0.99  --bmc1_incremental                      false
% 3.49/0.99  --bmc1_axioms                           reachable_all
% 3.49/0.99  --bmc1_min_bound                        0
% 3.49/0.99  --bmc1_max_bound                        -1
% 3.49/0.99  --bmc1_max_bound_default                -1
% 3.49/0.99  --bmc1_symbol_reachability              true
% 3.49/0.99  --bmc1_property_lemmas                  false
% 3.49/0.99  --bmc1_k_induction                      false
% 3.49/0.99  --bmc1_non_equiv_states                 false
% 3.49/0.99  --bmc1_deadlock                         false
% 3.49/0.99  --bmc1_ucm                              false
% 3.49/0.99  --bmc1_add_unsat_core                   none
% 3.49/0.99  --bmc1_unsat_core_children              false
% 3.49/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.49/0.99  --bmc1_out_stat                         full
% 3.49/0.99  --bmc1_ground_init                      false
% 3.49/0.99  --bmc1_pre_inst_next_state              false
% 3.49/0.99  --bmc1_pre_inst_state                   false
% 3.49/0.99  --bmc1_pre_inst_reach_state             false
% 3.49/0.99  --bmc1_out_unsat_core                   false
% 3.49/0.99  --bmc1_aig_witness_out                  false
% 3.49/0.99  --bmc1_verbose                          false
% 3.49/0.99  --bmc1_dump_clauses_tptp                false
% 3.49/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.49/0.99  --bmc1_dump_file                        -
% 3.49/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.49/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.49/0.99  --bmc1_ucm_extend_mode                  1
% 3.49/0.99  --bmc1_ucm_init_mode                    2
% 3.49/0.99  --bmc1_ucm_cone_mode                    none
% 3.49/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.49/0.99  --bmc1_ucm_relax_model                  4
% 3.49/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.49/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.49/0.99  --bmc1_ucm_layered_model                none
% 3.49/0.99  --bmc1_ucm_max_lemma_size               10
% 3.49/0.99  
% 3.49/0.99  ------ AIG Options
% 3.49/0.99  
% 3.49/0.99  --aig_mode                              false
% 3.49/0.99  
% 3.49/0.99  ------ Instantiation Options
% 3.49/0.99  
% 3.49/0.99  --instantiation_flag                    true
% 3.49/0.99  --inst_sos_flag                         true
% 3.49/0.99  --inst_sos_phase                        true
% 3.49/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.49/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.49/0.99  --inst_lit_sel_side                     none
% 3.49/0.99  --inst_solver_per_active                1400
% 3.49/0.99  --inst_solver_calls_frac                1.
% 3.49/0.99  --inst_passive_queue_type               priority_queues
% 3.49/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.49/0.99  --inst_passive_queues_freq              [25;2]
% 3.49/0.99  --inst_dismatching                      true
% 3.49/0.99  --inst_eager_unprocessed_to_passive     true
% 3.49/0.99  --inst_prop_sim_given                   true
% 3.49/0.99  --inst_prop_sim_new                     false
% 3.49/0.99  --inst_subs_new                         false
% 3.49/0.99  --inst_eq_res_simp                      false
% 3.49/0.99  --inst_subs_given                       false
% 3.49/0.99  --inst_orphan_elimination               true
% 3.49/0.99  --inst_learning_loop_flag               true
% 3.49/0.99  --inst_learning_start                   3000
% 3.49/0.99  --inst_learning_factor                  2
% 3.49/0.99  --inst_start_prop_sim_after_learn       3
% 3.49/0.99  --inst_sel_renew                        solver
% 3.49/0.99  --inst_lit_activity_flag                true
% 3.49/0.99  --inst_restr_to_given                   false
% 3.49/0.99  --inst_activity_threshold               500
% 3.49/0.99  --inst_out_proof                        true
% 3.49/0.99  
% 3.49/0.99  ------ Resolution Options
% 3.49/0.99  
% 3.49/0.99  --resolution_flag                       false
% 3.49/0.99  --res_lit_sel                           adaptive
% 3.49/0.99  --res_lit_sel_side                      none
% 3.49/0.99  --res_ordering                          kbo
% 3.49/0.99  --res_to_prop_solver                    active
% 3.49/0.99  --res_prop_simpl_new                    false
% 3.49/0.99  --res_prop_simpl_given                  true
% 3.49/0.99  --res_passive_queue_type                priority_queues
% 3.49/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.49/0.99  --res_passive_queues_freq               [15;5]
% 3.49/0.99  --res_forward_subs                      full
% 3.49/0.99  --res_backward_subs                     full
% 3.49/0.99  --res_forward_subs_resolution           true
% 3.49/0.99  --res_backward_subs_resolution          true
% 3.49/0.99  --res_orphan_elimination                true
% 3.49/0.99  --res_time_limit                        2.
% 3.49/0.99  --res_out_proof                         true
% 3.49/0.99  
% 3.49/0.99  ------ Superposition Options
% 3.49/0.99  
% 3.49/0.99  --superposition_flag                    true
% 3.49/0.99  --sup_passive_queue_type                priority_queues
% 3.49/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.49/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.49/0.99  --demod_completeness_check              fast
% 3.49/0.99  --demod_use_ground                      true
% 3.49/0.99  --sup_to_prop_solver                    passive
% 3.49/0.99  --sup_prop_simpl_new                    true
% 3.49/0.99  --sup_prop_simpl_given                  true
% 3.49/0.99  --sup_fun_splitting                     true
% 3.49/0.99  --sup_smt_interval                      50000
% 3.49/0.99  
% 3.49/0.99  ------ Superposition Simplification Setup
% 3.49/0.99  
% 3.49/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.49/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.49/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.49/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.49/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.49/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.49/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.49/0.99  --sup_immed_triv                        [TrivRules]
% 3.49/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.49/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.49/0.99  --sup_immed_bw_main                     []
% 3.49/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.49/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.49/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.49/0.99  --sup_input_bw                          []
% 3.49/0.99  
% 3.49/0.99  ------ Combination Options
% 3.49/0.99  
% 3.49/0.99  --comb_res_mult                         3
% 3.49/0.99  --comb_sup_mult                         2
% 3.49/0.99  --comb_inst_mult                        10
% 3.49/0.99  
% 3.49/0.99  ------ Debug Options
% 3.49/0.99  
% 3.49/0.99  --dbg_backtrace                         false
% 3.49/0.99  --dbg_dump_prop_clauses                 false
% 3.49/0.99  --dbg_dump_prop_clauses_file            -
% 3.49/0.99  --dbg_out_stat                          false
% 3.49/0.99  
% 3.49/0.99  
% 3.49/0.99  
% 3.49/0.99  
% 3.49/0.99  ------ Proving...
% 3.49/0.99  
% 3.49/0.99  
% 3.49/0.99  % SZS status Theorem for theBenchmark.p
% 3.49/0.99  
% 3.49/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.49/0.99  
% 3.49/0.99  fof(f23,conjecture,(
% 3.49/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 3.49/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/0.99  
% 3.49/0.99  fof(f24,negated_conjecture,(
% 3.49/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 3.49/0.99    inference(negated_conjecture,[],[f23])).
% 3.49/0.99  
% 3.49/0.99  fof(f25,plain,(
% 3.49/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 3.49/0.99    inference(pure_predicate_removal,[],[f24])).
% 3.49/0.99  
% 3.49/0.99  fof(f42,plain,(
% 3.49/0.99    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 3.49/0.99    inference(ennf_transformation,[],[f25])).
% 3.49/0.99  
% 3.49/0.99  fof(f43,plain,(
% 3.49/0.99    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 3.49/0.99    inference(flattening,[],[f42])).
% 3.49/0.99  
% 3.49/0.99  fof(f50,plain,(
% 3.49/0.99    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3))),
% 3.49/0.99    introduced(choice_axiom,[])).
% 3.49/0.99  
% 3.49/0.99  fof(f51,plain,(
% 3.49/0.99    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3)),
% 3.49/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f43,f50])).
% 3.49/0.99  
% 3.49/0.99  fof(f82,plain,(
% 3.49/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 3.49/0.99    inference(cnf_transformation,[],[f51])).
% 3.49/0.99  
% 3.49/0.99  fof(f3,axiom,(
% 3.49/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.49/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/0.99  
% 3.49/0.99  fof(f56,plain,(
% 3.49/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.49/0.99    inference(cnf_transformation,[],[f3])).
% 3.49/0.99  
% 3.49/0.99  fof(f4,axiom,(
% 3.49/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.49/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/0.99  
% 3.49/0.99  fof(f57,plain,(
% 3.49/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.49/0.99    inference(cnf_transformation,[],[f4])).
% 3.49/0.99  
% 3.49/0.99  fof(f5,axiom,(
% 3.49/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.49/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/0.99  
% 3.49/0.99  fof(f58,plain,(
% 3.49/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.49/0.99    inference(cnf_transformation,[],[f5])).
% 3.49/0.99  
% 3.49/0.99  fof(f6,axiom,(
% 3.49/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.49/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/0.99  
% 3.49/0.99  fof(f59,plain,(
% 3.49/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.49/0.99    inference(cnf_transformation,[],[f6])).
% 3.49/0.99  
% 3.49/0.99  fof(f7,axiom,(
% 3.49/0.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.49/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/0.99  
% 3.49/0.99  fof(f60,plain,(
% 3.49/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.49/0.99    inference(cnf_transformation,[],[f7])).
% 3.49/0.99  
% 3.49/0.99  fof(f8,axiom,(
% 3.49/0.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.49/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/0.99  
% 3.49/0.99  fof(f61,plain,(
% 3.49/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.49/0.99    inference(cnf_transformation,[],[f8])).
% 3.49/0.99  
% 3.49/0.99  fof(f9,axiom,(
% 3.49/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.49/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/0.99  
% 3.49/0.99  fof(f62,plain,(
% 3.49/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.49/0.99    inference(cnf_transformation,[],[f9])).
% 3.49/0.99  
% 3.49/0.99  fof(f85,plain,(
% 3.49/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.49/0.99    inference(definition_unfolding,[],[f61,f62])).
% 3.49/0.99  
% 3.49/0.99  fof(f86,plain,(
% 3.49/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.49/0.99    inference(definition_unfolding,[],[f60,f85])).
% 3.49/0.99  
% 3.49/0.99  fof(f87,plain,(
% 3.49/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.49/0.99    inference(definition_unfolding,[],[f59,f86])).
% 3.49/0.99  
% 3.49/0.99  fof(f88,plain,(
% 3.49/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.49/0.99    inference(definition_unfolding,[],[f58,f87])).
% 3.49/0.99  
% 3.49/0.99  fof(f89,plain,(
% 3.49/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.49/0.99    inference(definition_unfolding,[],[f57,f88])).
% 3.49/0.99  
% 3.49/0.99  fof(f90,plain,(
% 3.49/0.99    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.49/0.99    inference(definition_unfolding,[],[f56,f89])).
% 3.49/0.99  
% 3.49/0.99  fof(f96,plain,(
% 3.49/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))),
% 3.49/1.00    inference(definition_unfolding,[],[f82,f90])).
% 3.49/1.00  
% 3.49/1.00  fof(f20,axiom,(
% 3.49/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.49/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/1.00  
% 3.49/1.00  fof(f26,plain,(
% 3.49/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.49/1.00    inference(pure_predicate_removal,[],[f20])).
% 3.49/1.00  
% 3.49/1.00  fof(f38,plain,(
% 3.49/1.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.49/1.00    inference(ennf_transformation,[],[f26])).
% 3.49/1.00  
% 3.49/1.00  fof(f78,plain,(
% 3.49/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.49/1.00    inference(cnf_transformation,[],[f38])).
% 3.49/1.00  
% 3.49/1.00  fof(f12,axiom,(
% 3.49/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.49/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/1.00  
% 3.49/1.00  fof(f28,plain,(
% 3.49/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.49/1.00    inference(ennf_transformation,[],[f12])).
% 3.49/1.00  
% 3.49/1.00  fof(f48,plain,(
% 3.49/1.00    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.49/1.00    inference(nnf_transformation,[],[f28])).
% 3.49/1.00  
% 3.49/1.00  fof(f67,plain,(
% 3.49/1.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.49/1.00    inference(cnf_transformation,[],[f48])).
% 3.49/1.00  
% 3.49/1.00  fof(f10,axiom,(
% 3.49/1.00    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 3.49/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/1.00  
% 3.49/1.00  fof(f46,plain,(
% 3.49/1.00    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 3.49/1.00    inference(nnf_transformation,[],[f10])).
% 3.49/1.00  
% 3.49/1.00  fof(f47,plain,(
% 3.49/1.00    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 3.49/1.00    inference(flattening,[],[f46])).
% 3.49/1.00  
% 3.49/1.00  fof(f63,plain,(
% 3.49/1.00    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 3.49/1.00    inference(cnf_transformation,[],[f47])).
% 3.49/1.00  
% 3.49/1.00  fof(f93,plain,(
% 3.49/1.00    ( ! [X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 3.49/1.00    inference(definition_unfolding,[],[f63,f90,f90])).
% 3.49/1.00  
% 3.49/1.00  fof(f11,axiom,(
% 3.49/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.49/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/1.00  
% 3.49/1.00  fof(f27,plain,(
% 3.49/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.49/1.00    inference(ennf_transformation,[],[f11])).
% 3.49/1.00  
% 3.49/1.00  fof(f66,plain,(
% 3.49/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.49/1.00    inference(cnf_transformation,[],[f27])).
% 3.49/1.00  
% 3.49/1.00  fof(f13,axiom,(
% 3.49/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.49/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/1.00  
% 3.49/1.00  fof(f69,plain,(
% 3.49/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.49/1.00    inference(cnf_transformation,[],[f13])).
% 3.49/1.00  
% 3.49/1.00  fof(f1,axiom,(
% 3.49/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.49/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/1.00  
% 3.49/1.00  fof(f44,plain,(
% 3.49/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.49/1.00    inference(nnf_transformation,[],[f1])).
% 3.49/1.00  
% 3.49/1.00  fof(f45,plain,(
% 3.49/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.49/1.00    inference(flattening,[],[f44])).
% 3.49/1.00  
% 3.49/1.00  fof(f52,plain,(
% 3.49/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.49/1.00    inference(cnf_transformation,[],[f45])).
% 3.49/1.00  
% 3.49/1.00  fof(f98,plain,(
% 3.49/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.49/1.00    inference(equality_resolution,[],[f52])).
% 3.49/1.00  
% 3.49/1.00  fof(f2,axiom,(
% 3.49/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.49/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/1.00  
% 3.49/1.00  fof(f55,plain,(
% 3.49/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.49/1.00    inference(cnf_transformation,[],[f2])).
% 3.49/1.00  
% 3.49/1.00  fof(f22,axiom,(
% 3.49/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => (r1_tarski(X0,X3) => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 3.49/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/1.00  
% 3.49/1.00  fof(f40,plain,(
% 3.49/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 3.49/1.00    inference(ennf_transformation,[],[f22])).
% 3.49/1.00  
% 3.49/1.00  fof(f41,plain,(
% 3.49/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 3.49/1.00    inference(flattening,[],[f40])).
% 3.49/1.00  
% 3.49/1.00  fof(f80,plain,(
% 3.49/1.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 3.49/1.00    inference(cnf_transformation,[],[f41])).
% 3.49/1.00  
% 3.49/1.00  fof(f21,axiom,(
% 3.49/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.49/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/1.00  
% 3.49/1.00  fof(f39,plain,(
% 3.49/1.00    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.49/1.00    inference(ennf_transformation,[],[f21])).
% 3.49/1.00  
% 3.49/1.00  fof(f79,plain,(
% 3.49/1.00    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.49/1.00    inference(cnf_transformation,[],[f39])).
% 3.49/1.00  
% 3.49/1.00  fof(f18,axiom,(
% 3.49/1.00    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 3.49/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/1.00  
% 3.49/1.00  fof(f35,plain,(
% 3.49/1.00    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 3.49/1.00    inference(ennf_transformation,[],[f18])).
% 3.49/1.00  
% 3.49/1.00  fof(f76,plain,(
% 3.49/1.00    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 3.49/1.00    inference(cnf_transformation,[],[f35])).
% 3.49/1.00  
% 3.49/1.00  fof(f54,plain,(
% 3.49/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.49/1.00    inference(cnf_transformation,[],[f45])).
% 3.49/1.00  
% 3.49/1.00  fof(f14,axiom,(
% 3.49/1.00    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 3.49/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/1.00  
% 3.49/1.00  fof(f29,plain,(
% 3.49/1.00    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.49/1.00    inference(ennf_transformation,[],[f14])).
% 3.49/1.00  
% 3.49/1.00  fof(f70,plain,(
% 3.49/1.00    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.49/1.00    inference(cnf_transformation,[],[f29])).
% 3.49/1.00  
% 3.49/1.00  fof(f16,axiom,(
% 3.49/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 3.49/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/1.00  
% 3.49/1.00  fof(f32,plain,(
% 3.49/1.00    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.49/1.00    inference(ennf_transformation,[],[f16])).
% 3.49/1.00  
% 3.49/1.00  fof(f33,plain,(
% 3.49/1.00    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.49/1.00    inference(flattening,[],[f32])).
% 3.49/1.00  
% 3.49/1.00  fof(f73,plain,(
% 3.49/1.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.49/1.00    inference(cnf_transformation,[],[f33])).
% 3.49/1.00  
% 3.49/1.00  fof(f19,axiom,(
% 3.49/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 3.49/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/1.00  
% 3.49/1.00  fof(f36,plain,(
% 3.49/1.00    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.49/1.00    inference(ennf_transformation,[],[f19])).
% 3.49/1.00  
% 3.49/1.00  fof(f37,plain,(
% 3.49/1.00    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.49/1.00    inference(flattening,[],[f36])).
% 3.49/1.00  
% 3.49/1.00  fof(f77,plain,(
% 3.49/1.00    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.49/1.00    inference(cnf_transformation,[],[f37])).
% 3.49/1.00  
% 3.49/1.00  fof(f94,plain,(
% 3.49/1.00    ( ! [X0,X1] : (k6_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.49/1.00    inference(definition_unfolding,[],[f77,f90,f90])).
% 3.49/1.00  
% 3.49/1.00  fof(f81,plain,(
% 3.49/1.00    v1_funct_1(sK3)),
% 3.49/1.00    inference(cnf_transformation,[],[f51])).
% 3.49/1.00  
% 3.49/1.00  fof(f84,plain,(
% 3.49/1.00    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 3.49/1.00    inference(cnf_transformation,[],[f51])).
% 3.49/1.00  
% 3.49/1.00  fof(f95,plain,(
% 3.49/1.00    ~r1_tarski(k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 3.49/1.00    inference(definition_unfolding,[],[f84,f90,f90])).
% 3.49/1.00  
% 3.49/1.00  fof(f68,plain,(
% 3.49/1.00    ( ! [X0,X1] : (v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.49/1.00    inference(cnf_transformation,[],[f48])).
% 3.49/1.00  
% 3.49/1.00  fof(f15,axiom,(
% 3.49/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 3.49/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/1.00  
% 3.49/1.00  fof(f30,plain,(
% 3.49/1.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.49/1.00    inference(ennf_transformation,[],[f15])).
% 3.49/1.00  
% 3.49/1.00  fof(f31,plain,(
% 3.49/1.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.49/1.00    inference(flattening,[],[f30])).
% 3.49/1.00  
% 3.49/1.00  fof(f71,plain,(
% 3.49/1.00    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.49/1.00    inference(cnf_transformation,[],[f31])).
% 3.49/1.00  
% 3.49/1.00  fof(f17,axiom,(
% 3.49/1.00    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 3.49/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/1.00  
% 3.49/1.00  fof(f34,plain,(
% 3.49/1.00    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.49/1.00    inference(ennf_transformation,[],[f17])).
% 3.49/1.00  
% 3.49/1.00  fof(f49,plain,(
% 3.49/1.00    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.49/1.00    inference(nnf_transformation,[],[f34])).
% 3.49/1.00  
% 3.49/1.00  fof(f74,plain,(
% 3.49/1.00    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.49/1.00    inference(cnf_transformation,[],[f49])).
% 3.49/1.00  
% 3.49/1.00  cnf(c_24,negated_conjecture,
% 3.49/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) ),
% 3.49/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_921,plain,
% 3.49/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
% 3.49/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_19,plain,
% 3.49/1.00      ( v4_relat_1(X0,X1)
% 3.49/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.49/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_925,plain,
% 3.49/1.00      ( v4_relat_1(X0,X1) = iProver_top
% 3.49/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 3.49/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_1485,plain,
% 3.49/1.00      ( v4_relat_1(sK3,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
% 3.49/1.00      inference(superposition,[status(thm)],[c_921,c_925]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_9,plain,
% 3.49/1.00      ( ~ v4_relat_1(X0,X1)
% 3.49/1.00      | r1_tarski(k1_relat_1(X0),X1)
% 3.49/1.00      | ~ v1_relat_1(X0) ),
% 3.49/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_934,plain,
% 3.49/1.00      ( v4_relat_1(X0,X1) != iProver_top
% 3.49/1.00      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 3.49/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.49/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_6,plain,
% 3.49/1.00      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
% 3.49/1.00      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
% 3.49/1.00      | k1_xboole_0 = X0 ),
% 3.49/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_937,plain,
% 3.49/1.00      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
% 3.49/1.00      | k1_xboole_0 = X1
% 3.49/1.00      | r1_tarski(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
% 3.49/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_2649,plain,
% 3.49/1.00      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_relat_1(X1)
% 3.49/1.00      | k1_relat_1(X1) = k1_xboole_0
% 3.49/1.00      | v4_relat_1(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top
% 3.49/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.49/1.00      inference(superposition,[status(thm)],[c_934,c_937]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_7932,plain,
% 3.49/1.00      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
% 3.49/1.00      | k1_relat_1(sK3) = k1_xboole_0
% 3.49/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.49/1.00      inference(superposition,[status(thm)],[c_1485,c_2649]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_7,plain,
% 3.49/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.49/1.00      | ~ v1_relat_1(X1)
% 3.49/1.00      | v1_relat_1(X0) ),
% 3.49/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_982,plain,
% 3.49/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
% 3.49/1.00      | ~ v1_relat_1(X0)
% 3.49/1.00      | v1_relat_1(sK3) ),
% 3.49/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_1039,plain,
% 3.49/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.49/1.00      | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 3.49/1.00      | v1_relat_1(sK3) ),
% 3.49/1.00      inference(instantiation,[status(thm)],[c_982]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_1151,plain,
% 3.49/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))
% 3.49/1.00      | ~ v1_relat_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))
% 3.49/1.00      | v1_relat_1(sK3) ),
% 3.49/1.00      inference(instantiation,[status(thm)],[c_1039]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_10,plain,
% 3.49/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.49/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_1185,plain,
% 3.49/1.00      ( v1_relat_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
% 3.49/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_7940,plain,
% 3.49/1.00      ( ~ v1_relat_1(sK3)
% 3.49/1.00      | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
% 3.49/1.00      | k1_relat_1(sK3) = k1_xboole_0 ),
% 3.49/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_7932]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_8135,plain,
% 3.49/1.00      ( k1_relat_1(sK3) = k1_xboole_0
% 3.49/1.00      | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(sK3) ),
% 3.49/1.00      inference(global_propositional_subsumption,
% 3.49/1.00                [status(thm)],
% 3.49/1.00                [c_7932,c_24,c_1151,c_1185,c_7940]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_8136,plain,
% 3.49/1.00      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
% 3.49/1.00      | k1_relat_1(sK3) = k1_xboole_0 ),
% 3.49/1.00      inference(renaming,[status(thm)],[c_8135]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_2,plain,
% 3.49/1.00      ( r1_tarski(X0,X0) ),
% 3.49/1.00      inference(cnf_transformation,[],[f98]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_941,plain,
% 3.49/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 3.49/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_3,plain,
% 3.49/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 3.49/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_940,plain,
% 3.49/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.49/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_21,plain,
% 3.49/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.49/1.00      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.49/1.00      | ~ r1_tarski(X3,X0) ),
% 3.49/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_923,plain,
% 3.49/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.49/1.00      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.49/1.00      | r1_tarski(X3,X0) != iProver_top ),
% 3.49/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_1375,plain,
% 3.49/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) = iProver_top
% 3.49/1.00      | r1_tarski(X0,sK3) != iProver_top ),
% 3.49/1.00      inference(superposition,[status(thm)],[c_921,c_923]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_1621,plain,
% 3.49/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) = iProver_top
% 3.49/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.49/1.00      | r1_tarski(X1,sK3) != iProver_top ),
% 3.49/1.00      inference(superposition,[status(thm)],[c_1375,c_923]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_1717,plain,
% 3.49/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) = iProver_top
% 3.49/1.00      | r1_tarski(X0,sK3) != iProver_top ),
% 3.49/1.00      inference(superposition,[status(thm)],[c_940,c_1621]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_1726,plain,
% 3.49/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
% 3.49/1.00      inference(superposition,[status(thm)],[c_941,c_1717]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_20,plain,
% 3.49/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.49/1.00      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.49/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_924,plain,
% 3.49/1.00      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.49/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.49/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_2168,plain,
% 3.49/1.00      ( k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,k1_xboole_0,X0) = k9_relat_1(k1_xboole_0,X0) ),
% 3.49/1.00      inference(superposition,[status(thm)],[c_1726,c_924]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_17,plain,
% 3.49/1.00      ( r1_tarski(k7_relat_1(X0,X1),X0) | ~ v1_relat_1(X0) ),
% 3.49/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_926,plain,
% 3.49/1.00      ( r1_tarski(k7_relat_1(X0,X1),X0) = iProver_top
% 3.49/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.49/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_0,plain,
% 3.49/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.49/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_942,plain,
% 3.49/1.00      ( X0 = X1
% 3.49/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.49/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.49/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_2037,plain,
% 3.49/1.00      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.49/1.00      inference(superposition,[status(thm)],[c_940,c_942]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_3243,plain,
% 3.49/1.00      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
% 3.49/1.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.49/1.00      inference(superposition,[status(thm)],[c_926,c_2037]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_1186,plain,
% 3.49/1.00      ( v1_relat_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) = iProver_top ),
% 3.49/1.00      inference(predicate_to_equality,[status(thm)],[c_1185]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_1208,plain,
% 3.49/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.49/1.00      | v1_relat_1(X0)
% 3.49/1.00      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 3.49/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_2008,plain,
% 3.49/1.00      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))
% 3.49/1.00      | ~ v1_relat_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))
% 3.49/1.00      | v1_relat_1(k1_xboole_0) ),
% 3.49/1.00      inference(instantiation,[status(thm)],[c_1208]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_2009,plain,
% 3.49/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) != iProver_top
% 3.49/1.00      | v1_relat_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != iProver_top
% 3.49/1.00      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.49/1.00      inference(predicate_to_equality,[status(thm)],[c_2008]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_3251,plain,
% 3.49/1.00      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.49/1.00      inference(global_propositional_subsumption,
% 3.49/1.00                [status(thm)],
% 3.49/1.00                [c_3243,c_1186,c_1726,c_2009]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_936,plain,
% 3.49/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.49/1.00      | v1_relat_1(X1) != iProver_top
% 3.49/1.00      | v1_relat_1(X0) = iProver_top ),
% 3.49/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_2154,plain,
% 3.49/1.00      ( r1_tarski(X0,sK3) != iProver_top
% 3.49/1.00      | v1_relat_1(X0) = iProver_top
% 3.49/1.00      | v1_relat_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != iProver_top ),
% 3.49/1.00      inference(superposition,[status(thm)],[c_1375,c_936]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_2463,plain,
% 3.49/1.00      ( v1_relat_1(X0) = iProver_top | r1_tarski(X0,sK3) != iProver_top ),
% 3.49/1.00      inference(global_propositional_subsumption,
% 3.49/1.00                [status(thm)],
% 3.49/1.00                [c_2154,c_1186]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_2464,plain,
% 3.49/1.00      ( r1_tarski(X0,sK3) != iProver_top | v1_relat_1(X0) = iProver_top ),
% 3.49/1.00      inference(renaming,[status(thm)],[c_2463]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_2470,plain,
% 3.49/1.00      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.49/1.00      inference(superposition,[status(thm)],[c_940,c_2464]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_11,plain,
% 3.49/1.00      ( ~ v1_relat_1(X0)
% 3.49/1.00      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 3.49/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_932,plain,
% 3.49/1.00      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 3.49/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.49/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_2477,plain,
% 3.49/1.00      ( k2_relat_1(k7_relat_1(k1_xboole_0,X0)) = k9_relat_1(k1_xboole_0,X0) ),
% 3.49/1.00      inference(superposition,[status(thm)],[c_2470,c_932]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_3254,plain,
% 3.49/1.00      ( k9_relat_1(k1_xboole_0,X0) = k2_relat_1(k1_xboole_0) ),
% 3.49/1.00      inference(demodulation,[status(thm)],[c_3251,c_2477]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_4506,plain,
% 3.49/1.00      ( k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,k1_xboole_0,X0) = k2_relat_1(k1_xboole_0) ),
% 3.49/1.00      inference(light_normalisation,[status(thm)],[c_2168,c_2168,c_3254]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_8155,plain,
% 3.49/1.00      ( k7_relset_1(k1_relat_1(sK3),sK1,k1_xboole_0,X0) = k2_relat_1(k1_xboole_0)
% 3.49/1.00      | k1_relat_1(sK3) = k1_xboole_0 ),
% 3.49/1.00      inference(superposition,[status(thm)],[c_8136,c_4506]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_27,plain,
% 3.49/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
% 3.49/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_1152,plain,
% 3.49/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) != iProver_top
% 3.49/1.00      | v1_relat_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != iProver_top
% 3.49/1.00      | v1_relat_1(sK3) = iProver_top ),
% 3.49/1.00      inference(predicate_to_equality,[status(thm)],[c_1151]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_2153,plain,
% 3.49/1.00      ( v1_relat_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != iProver_top
% 3.49/1.00      | v1_relat_1(sK3) = iProver_top ),
% 3.49/1.00      inference(superposition,[status(thm)],[c_921,c_936]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_2238,plain,
% 3.49/1.00      ( v1_relat_1(sK3) = iProver_top ),
% 3.49/1.00      inference(global_propositional_subsumption,
% 3.49/1.00                [status(thm)],
% 3.49/1.00                [c_2153,c_27,c_1152,c_1186]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_2242,plain,
% 3.49/1.00      ( k2_relat_1(k7_relat_1(sK3,X0)) = k9_relat_1(sK3,X0) ),
% 3.49/1.00      inference(superposition,[status(thm)],[c_2238,c_932]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_13,plain,
% 3.49/1.00      ( ~ r1_tarski(X0,X1)
% 3.49/1.00      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 3.49/1.00      | ~ v1_relat_1(X0)
% 3.49/1.00      | ~ v1_relat_1(X1) ),
% 3.49/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_930,plain,
% 3.49/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.49/1.00      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
% 3.49/1.00      | v1_relat_1(X0) != iProver_top
% 3.49/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.49/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_2546,plain,
% 3.49/1.00      ( r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(X1)) = iProver_top
% 3.49/1.00      | r1_tarski(k7_relat_1(sK3,X0),X1) != iProver_top
% 3.49/1.00      | v1_relat_1(X1) != iProver_top
% 3.49/1.00      | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
% 3.49/1.00      inference(superposition,[status(thm)],[c_2242,c_930]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_2471,plain,
% 3.49/1.00      ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top
% 3.49/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.49/1.00      inference(superposition,[status(thm)],[c_926,c_2464]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_3112,plain,
% 3.49/1.00      ( v1_relat_1(X1) != iProver_top
% 3.49/1.00      | r1_tarski(k7_relat_1(sK3,X0),X1) != iProver_top
% 3.49/1.00      | r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(X1)) = iProver_top ),
% 3.49/1.00      inference(global_propositional_subsumption,
% 3.49/1.00                [status(thm)],
% 3.49/1.00                [c_2546,c_27,c_1152,c_1186,c_2471]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_3113,plain,
% 3.49/1.00      ( r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(X1)) = iProver_top
% 3.49/1.00      | r1_tarski(k7_relat_1(sK3,X0),X1) != iProver_top
% 3.49/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.49/1.00      inference(renaming,[status(thm)],[c_3112]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_18,plain,
% 3.49/1.00      ( ~ v1_funct_1(X0)
% 3.49/1.00      | ~ v1_relat_1(X0)
% 3.49/1.00      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k1_relat_1(X0)
% 3.49/1.00      | k6_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
% 3.49/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_25,negated_conjecture,
% 3.49/1.00      ( v1_funct_1(sK3) ),
% 3.49/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_277,plain,
% 3.49/1.00      ( ~ v1_relat_1(X0)
% 3.49/1.00      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k1_relat_1(X0)
% 3.49/1.00      | k6_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
% 3.49/1.00      | sK3 != X0 ),
% 3.49/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_25]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_278,plain,
% 3.49/1.00      ( ~ v1_relat_1(sK3)
% 3.49/1.00      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(sK3)
% 3.49/1.00      | k6_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
% 3.49/1.00      inference(unflattening,[status(thm)],[c_277]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_920,plain,
% 3.49/1.00      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(sK3)
% 3.49/1.00      | k6_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
% 3.49/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.49/1.00      inference(predicate_to_equality,[status(thm)],[c_278]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_8139,plain,
% 3.49/1.00      ( k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
% 3.49/1.00      | k1_relat_1(sK3) = k1_xboole_0
% 3.49/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.49/1.00      inference(superposition,[status(thm)],[c_8136,c_920]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_8403,plain,
% 3.49/1.00      ( k1_relat_1(sK3) = k1_xboole_0
% 3.49/1.00      | k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) ),
% 3.49/1.00      inference(global_propositional_subsumption,
% 3.49/1.00                [status(thm)],
% 3.49/1.00                [c_8139,c_27,c_1152,c_1186]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_8404,plain,
% 3.49/1.00      ( k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
% 3.49/1.00      | k1_relat_1(sK3) = k1_xboole_0 ),
% 3.49/1.00      inference(renaming,[status(thm)],[c_8403]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_2166,plain,
% 3.49/1.00      ( k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
% 3.49/1.00      inference(superposition,[status(thm)],[c_921,c_924]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_22,negated_conjecture,
% 3.49/1.00      ( ~ r1_tarski(k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
% 3.49/1.00      inference(cnf_transformation,[],[f95]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_922,plain,
% 3.49/1.00      ( r1_tarski(k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 3.49/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_2235,plain,
% 3.49/1.00      ( r1_tarski(k9_relat_1(sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 3.49/1.00      inference(demodulation,[status(thm)],[c_2166,c_922]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_8408,plain,
% 3.49/1.00      ( k1_relat_1(sK3) = k1_xboole_0
% 3.49/1.00      | r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) != iProver_top ),
% 3.49/1.00      inference(superposition,[status(thm)],[c_8404,c_2235]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_8418,plain,
% 3.49/1.00      ( k1_relat_1(sK3) = k1_xboole_0
% 3.49/1.00      | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
% 3.49/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.49/1.00      inference(superposition,[status(thm)],[c_3113,c_8408]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_8915,plain,
% 3.49/1.00      ( r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
% 3.49/1.00      | k1_relat_1(sK3) = k1_xboole_0 ),
% 3.49/1.00      inference(global_propositional_subsumption,
% 3.49/1.00                [status(thm)],
% 3.49/1.00                [c_8418,c_27,c_1152,c_1186]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_8916,plain,
% 3.49/1.00      ( k1_relat_1(sK3) = k1_xboole_0
% 3.49/1.00      | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top ),
% 3.49/1.00      inference(renaming,[status(thm)],[c_8915]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_8919,plain,
% 3.49/1.00      ( k1_relat_1(sK3) = k1_xboole_0 | v1_relat_1(sK3) != iProver_top ),
% 3.49/1.00      inference(superposition,[status(thm)],[c_926,c_8916]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_9045,plain,
% 3.49/1.00      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 3.49/1.00      inference(global_propositional_subsumption,
% 3.49/1.00                [status(thm)],
% 3.49/1.00                [c_8155,c_27,c_1152,c_1186,c_8919]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_8,plain,
% 3.49/1.00      ( v4_relat_1(X0,X1)
% 3.49/1.00      | ~ r1_tarski(k1_relat_1(X0),X1)
% 3.49/1.00      | ~ v1_relat_1(X0) ),
% 3.49/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_935,plain,
% 3.49/1.00      ( v4_relat_1(X0,X1) = iProver_top
% 3.49/1.00      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.49/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.49/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_9086,plain,
% 3.49/1.00      ( v4_relat_1(sK3,X0) = iProver_top
% 3.49/1.00      | r1_tarski(k1_xboole_0,X0) != iProver_top
% 3.49/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.49/1.00      inference(superposition,[status(thm)],[c_9045,c_935]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_79,plain,
% 3.49/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.49/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_9511,plain,
% 3.49/1.00      ( v4_relat_1(sK3,X0) = iProver_top ),
% 3.49/1.00      inference(global_propositional_subsumption,
% 3.49/1.00                [status(thm)],
% 3.49/1.00                [c_9086,c_27,c_79,c_1152,c_1186]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_12,plain,
% 3.49/1.00      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 3.49/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_931,plain,
% 3.49/1.00      ( k7_relat_1(X0,X1) = X0
% 3.49/1.00      | v4_relat_1(X0,X1) != iProver_top
% 3.49/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.49/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_9518,plain,
% 3.49/1.00      ( k7_relat_1(sK3,X0) = sK3 | v1_relat_1(sK3) != iProver_top ),
% 3.49/1.00      inference(superposition,[status(thm)],[c_9511,c_931]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_2071,plain,
% 3.49/1.00      ( ~ v4_relat_1(sK3,X0)
% 3.49/1.00      | ~ v1_relat_1(sK3)
% 3.49/1.00      | k7_relat_1(sK3,X0) = sK3 ),
% 3.49/1.00      inference(instantiation,[status(thm)],[c_12]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_2072,plain,
% 3.49/1.00      ( k7_relat_1(sK3,X0) = sK3
% 3.49/1.00      | v4_relat_1(sK3,X0) != iProver_top
% 3.49/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.49/1.00      inference(predicate_to_equality,[status(thm)],[c_2071]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_9535,plain,
% 3.49/1.00      ( k7_relat_1(sK3,X0) = sK3 ),
% 3.49/1.00      inference(global_propositional_subsumption,
% 3.49/1.00                [status(thm)],
% 3.49/1.00                [c_9518,c_27,c_79,c_1152,c_1186,c_2072,c_9086]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_9559,plain,
% 3.49/1.00      ( k9_relat_1(sK3,X0) = k2_relat_1(sK3) ),
% 3.49/1.00      inference(demodulation,[status(thm)],[c_9535,c_2242]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_16,plain,
% 3.49/1.00      ( ~ v1_relat_1(X0)
% 3.49/1.00      | k2_relat_1(X0) = k1_xboole_0
% 3.49/1.00      | k1_relat_1(X0) != k1_xboole_0 ),
% 3.49/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_927,plain,
% 3.49/1.00      ( k2_relat_1(X0) = k1_xboole_0
% 3.49/1.00      | k1_relat_1(X0) != k1_xboole_0
% 3.49/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.49/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_9089,plain,
% 3.49/1.00      ( k2_relat_1(sK3) = k1_xboole_0 | v1_relat_1(sK3) != iProver_top ),
% 3.49/1.00      inference(superposition,[status(thm)],[c_9045,c_927]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_3104,plain,
% 3.49/1.00      ( ~ v1_relat_1(sK3)
% 3.49/1.00      | k2_relat_1(sK3) = k1_xboole_0
% 3.49/1.00      | k1_relat_1(sK3) != k1_xboole_0 ),
% 3.49/1.00      inference(instantiation,[status(thm)],[c_16]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_9339,plain,
% 3.49/1.00      ( k2_relat_1(sK3) = k1_xboole_0 ),
% 3.49/1.00      inference(global_propositional_subsumption,
% 3.49/1.00                [status(thm)],
% 3.49/1.00                [c_9089,c_24,c_27,c_1151,c_1152,c_1185,c_1186,c_3104,
% 3.49/1.00                 c_8919]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_9562,plain,
% 3.49/1.00      ( k9_relat_1(sK3,X0) = k1_xboole_0 ),
% 3.49/1.00      inference(light_normalisation,[status(thm)],[c_9559,c_9339]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_11248,plain,
% 3.49/1.00      ( r1_tarski(k1_xboole_0,k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 3.49/1.00      inference(demodulation,[status(thm)],[c_9562,c_2235]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_4550,plain,
% 3.49/1.00      ( r1_tarski(k1_xboole_0,k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
% 3.49/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_4551,plain,
% 3.49/1.00      ( r1_tarski(k1_xboole_0,k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) = iProver_top ),
% 3.49/1.00      inference(predicate_to_equality,[status(thm)],[c_4550]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(contradiction,plain,
% 3.49/1.00      ( $false ),
% 3.49/1.00      inference(minisat,[status(thm)],[c_11248,c_4551]) ).
% 3.49/1.00  
% 3.49/1.00  
% 3.49/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.49/1.00  
% 3.49/1.00  ------                               Statistics
% 3.49/1.00  
% 3.49/1.00  ------ General
% 3.49/1.00  
% 3.49/1.00  abstr_ref_over_cycles:                  0
% 3.49/1.00  abstr_ref_under_cycles:                 0
% 3.49/1.00  gc_basic_clause_elim:                   0
% 3.49/1.00  forced_gc_time:                         0
% 3.49/1.00  parsing_time:                           0.01
% 3.49/1.00  unif_index_cands_time:                  0.
% 3.49/1.00  unif_index_add_time:                    0.
% 3.49/1.00  orderings_time:                         0.
% 3.49/1.00  out_proof_time:                         0.013
% 3.49/1.00  total_time:                             0.455
% 3.49/1.00  num_of_symbols:                         50
% 3.49/1.00  num_of_terms:                           10297
% 3.49/1.00  
% 3.49/1.00  ------ Preprocessing
% 3.49/1.00  
% 3.49/1.00  num_of_splits:                          0
% 3.49/1.00  num_of_split_atoms:                     0
% 3.49/1.00  num_of_reused_defs:                     0
% 3.49/1.00  num_eq_ax_congr_red:                    19
% 3.49/1.00  num_of_sem_filtered_clauses:            1
% 3.49/1.00  num_of_subtypes:                        0
% 3.49/1.00  monotx_restored_types:                  0
% 3.49/1.00  sat_num_of_epr_types:                   0
% 3.49/1.00  sat_num_of_non_cyclic_types:            0
% 3.49/1.00  sat_guarded_non_collapsed_types:        0
% 3.49/1.00  num_pure_diseq_elim:                    0
% 3.49/1.00  simp_replaced_by:                       0
% 3.49/1.00  res_preprocessed:                       122
% 3.49/1.00  prep_upred:                             0
% 3.49/1.00  prep_unflattend:                        1
% 3.49/1.00  smt_new_axioms:                         0
% 3.49/1.00  pred_elim_cands:                        4
% 3.49/1.00  pred_elim:                              1
% 3.49/1.00  pred_elim_cl:                           1
% 3.49/1.00  pred_elim_cycles:                       3
% 3.49/1.00  merged_defs:                            0
% 3.49/1.00  merged_defs_ncl:                        0
% 3.49/1.00  bin_hyper_res:                          0
% 3.49/1.00  prep_cycles:                            4
% 3.49/1.00  pred_elim_time:                         0.002
% 3.49/1.00  splitting_time:                         0.
% 3.49/1.00  sem_filter_time:                        0.
% 3.49/1.00  monotx_time:                            0.
% 3.49/1.00  subtype_inf_time:                       0.
% 3.49/1.00  
% 3.49/1.00  ------ Problem properties
% 3.49/1.00  
% 3.49/1.00  clauses:                                24
% 3.49/1.00  conjectures:                            3
% 3.49/1.00  epr:                                    4
% 3.49/1.00  horn:                                   23
% 3.49/1.00  ground:                                 3
% 3.49/1.00  unary:                                  8
% 3.49/1.00  binary:                                 4
% 3.49/1.00  lits:                                   54
% 3.49/1.00  lits_eq:                                13
% 3.49/1.00  fd_pure:                                0
% 3.49/1.00  fd_pseudo:                              0
% 3.49/1.00  fd_cond:                                0
% 3.49/1.00  fd_pseudo_cond:                         2
% 3.49/1.00  ac_symbols:                             0
% 3.49/1.00  
% 3.49/1.00  ------ Propositional Solver
% 3.49/1.00  
% 3.49/1.00  prop_solver_calls:                      34
% 3.49/1.00  prop_fast_solver_calls:                 1326
% 3.49/1.00  smt_solver_calls:                       0
% 3.49/1.00  smt_fast_solver_calls:                  0
% 3.49/1.00  prop_num_of_clauses:                    5595
% 3.49/1.00  prop_preprocess_simplified:             9348
% 3.49/1.00  prop_fo_subsumed:                       96
% 3.49/1.00  prop_solver_time:                       0.
% 3.49/1.00  smt_solver_time:                        0.
% 3.49/1.00  smt_fast_solver_time:                   0.
% 3.49/1.00  prop_fast_solver_time:                  0.
% 3.49/1.00  prop_unsat_core_time:                   0.
% 3.49/1.00  
% 3.49/1.00  ------ QBF
% 3.49/1.00  
% 3.49/1.00  qbf_q_res:                              0
% 3.49/1.00  qbf_num_tautologies:                    0
% 3.49/1.00  qbf_prep_cycles:                        0
% 3.49/1.00  
% 3.49/1.00  ------ BMC1
% 3.49/1.00  
% 3.49/1.00  bmc1_current_bound:                     -1
% 3.49/1.00  bmc1_last_solved_bound:                 -1
% 3.49/1.00  bmc1_unsat_core_size:                   -1
% 3.49/1.00  bmc1_unsat_core_parents_size:           -1
% 3.49/1.00  bmc1_merge_next_fun:                    0
% 3.49/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.49/1.00  
% 3.49/1.00  ------ Instantiation
% 3.49/1.00  
% 3.49/1.00  inst_num_of_clauses:                    1310
% 3.49/1.00  inst_num_in_passive:                    351
% 3.49/1.00  inst_num_in_active:                     868
% 3.49/1.00  inst_num_in_unprocessed:                91
% 3.49/1.00  inst_num_of_loops:                      930
% 3.49/1.00  inst_num_of_learning_restarts:          0
% 3.49/1.00  inst_num_moves_active_passive:          56
% 3.49/1.00  inst_lit_activity:                      0
% 3.49/1.00  inst_lit_activity_moves:                0
% 3.49/1.00  inst_num_tautologies:                   0
% 3.49/1.00  inst_num_prop_implied:                  0
% 3.49/1.00  inst_num_existing_simplified:           0
% 3.49/1.00  inst_num_eq_res_simplified:             0
% 3.49/1.00  inst_num_child_elim:                    0
% 3.49/1.00  inst_num_of_dismatching_blockings:      622
% 3.49/1.00  inst_num_of_non_proper_insts:           2104
% 3.49/1.00  inst_num_of_duplicates:                 0
% 3.49/1.00  inst_inst_num_from_inst_to_res:         0
% 3.49/1.00  inst_dismatching_checking_time:         0.
% 3.49/1.00  
% 3.49/1.00  ------ Resolution
% 3.49/1.00  
% 3.49/1.00  res_num_of_clauses:                     0
% 3.49/1.00  res_num_in_passive:                     0
% 3.49/1.00  res_num_in_active:                      0
% 3.49/1.00  res_num_of_loops:                       126
% 3.49/1.00  res_forward_subset_subsumed:            269
% 3.49/1.00  res_backward_subset_subsumed:           2
% 3.49/1.00  res_forward_subsumed:                   0
% 3.49/1.00  res_backward_subsumed:                  0
% 3.49/1.00  res_forward_subsumption_resolution:     0
% 3.49/1.00  res_backward_subsumption_resolution:    0
% 3.49/1.00  res_clause_to_clause_subsumption:       1369
% 3.49/1.00  res_orphan_elimination:                 0
% 3.49/1.00  res_tautology_del:                      182
% 3.49/1.00  res_num_eq_res_simplified:              0
% 3.49/1.00  res_num_sel_changes:                    0
% 3.49/1.00  res_moves_from_active_to_pass:          0
% 3.49/1.00  
% 3.49/1.00  ------ Superposition
% 3.49/1.00  
% 3.49/1.00  sup_time_total:                         0.
% 3.49/1.00  sup_time_generating:                    0.
% 3.49/1.00  sup_time_sim_full:                      0.
% 3.49/1.00  sup_time_sim_immed:                     0.
% 3.49/1.00  
% 3.49/1.00  sup_num_of_clauses:                     263
% 3.49/1.00  sup_num_in_active:                      97
% 3.49/1.00  sup_num_in_passive:                     166
% 3.49/1.00  sup_num_of_loops:                       184
% 3.49/1.00  sup_fw_superposition:                   354
% 3.49/1.00  sup_bw_superposition:                   367
% 3.49/1.00  sup_immediate_simplified:               335
% 3.49/1.00  sup_given_eliminated:                   1
% 3.49/1.00  comparisons_done:                       0
% 3.49/1.00  comparisons_avoided:                    12
% 3.49/1.00  
% 3.49/1.00  ------ Simplifications
% 3.49/1.00  
% 3.49/1.00  
% 3.49/1.00  sim_fw_subset_subsumed:                 79
% 3.49/1.00  sim_bw_subset_subsumed:                 56
% 3.49/1.00  sim_fw_subsumed:                        96
% 3.49/1.00  sim_bw_subsumed:                        6
% 3.49/1.00  sim_fw_subsumption_res:                 0
% 3.49/1.00  sim_bw_subsumption_res:                 0
% 3.49/1.00  sim_tautology_del:                      2
% 3.49/1.00  sim_eq_tautology_del:                   64
% 3.49/1.00  sim_eq_res_simp:                        0
% 3.49/1.00  sim_fw_demodulated:                     85
% 3.49/1.00  sim_bw_demodulated:                     76
% 3.49/1.00  sim_light_normalised:                   134
% 3.49/1.00  sim_joinable_taut:                      0
% 3.49/1.00  sim_joinable_simp:                      0
% 3.49/1.00  sim_ac_normalised:                      0
% 3.49/1.00  sim_smt_subsumption:                    0
% 3.49/1.00  
%------------------------------------------------------------------------------
