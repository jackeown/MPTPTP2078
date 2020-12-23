%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:50 EST 2020

% Result     : Theorem 7.34s
% Output     : CNFRefutation 7.34s
% Verified   : 
% Statistics : Number of formulae       :  201 (3341 expanded)
%              Number of clauses        :  100 ( 702 expanded)
%              Number of leaves         :   27 ( 849 expanded)
%              Depth                    :   29
%              Number of atoms          :  571 (6727 expanded)
%              Number of equality atoms :  322 (3306 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f31,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f31])).

fof(f34,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(pure_predicate_removal,[],[f32])).

fof(f55,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f56,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f55])).

fof(f67,plain,
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

fof(f68,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f56,f67])).

fof(f123,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f68])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f126,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f78,f79])).

fof(f127,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f77,f126])).

fof(f128,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f76,f127])).

fof(f129,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f75,f128])).

fof(f130,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f74,f129])).

fof(f131,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f73,f130])).

fof(f143,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f123,f131])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f97,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f11,axiom,(
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

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f61,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f62,plain,(
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
    inference(flattening,[],[f61])).

fof(f83,plain,(
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
    inference(cnf_transformation,[],[f62])).

fof(f140,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = X3
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2) = X3
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = X3
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = X3
      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = X3
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X3
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X3
      | k1_xboole_0 = X3
      | ~ r1_tarski(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ) ),
    inference(definition_unfolding,[],[f83,f129,f130,f130,f130,f131,f131,f131,f129])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f96,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f94,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f18,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f101,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f48])).

fof(f112,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f141,plain,(
    ! [X0,X1] :
      ( k6_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f112,f131,f131])).

fof(f122,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f68])).

fof(f29,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f119,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f125,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f68])).

fof(f142,plain,(
    ~ r1_tarski(k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f125,f131,f131])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f57])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f145,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f69])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_1(X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f30])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f53])).

fof(f121,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f44])).

fof(f105,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f103,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f102,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f24,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f46])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( ( k1_funct_1(X0,X1) = X2
                | k1_xboole_0 != X2 )
              & ( k1_xboole_0 = X2
                | k1_funct_1(X0,X1) != X2 ) )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( ( k1_funct_1(X0,X1) = X2
                | ~ r2_hidden(k4_tarski(X1,X2),X0) )
              & ( r2_hidden(k4_tarski(X1,X2),X0)
                | k1_funct_1(X0,X1) != X2 ) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,X1) = X2
      | k1_xboole_0 != X2
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f156,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_funct_1(X0,X1)
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f111])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f27,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f71,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f59])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f147,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f81])).

fof(f21,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f104,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_48,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) ),
    inference(cnf_transformation,[],[f143])).

cnf(c_2087,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_42,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_2090,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_3638,plain,
    ( v4_relat_1(sK3,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2087,c_2090])).

cnf(c_22,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_2097,plain,
    ( v4_relat_1(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3) = X0
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3) = X0
    | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3) = X0
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = X0
    | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) = X0
    | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = X0
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f140])).

cnf(c_2103,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = X3
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2) = X3
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = X3
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = X3
    | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = X3
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X3
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X3
    | k1_xboole_0 = X3
    | r1_tarski(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_9679,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_relat_1(X1)
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X2,X3) = k1_relat_1(X1)
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X3) = k1_relat_1(X1)
    | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3) = k1_relat_1(X1)
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2) = k1_relat_1(X1)
    | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) = k1_relat_1(X1)
    | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = k1_relat_1(X1)
    | k1_relat_1(X1) = k1_xboole_0
    | v4_relat_1(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X2,X3)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2097,c_2103])).

cnf(c_28010,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3638,c_9679])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2100,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3419,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2087,c_2100])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_17,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_331,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_17])).

cnf(c_332,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_331])).

cnf(c_407,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_20,c_332])).

cnf(c_2086,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_407])).

cnf(c_3481,plain,
    ( v1_relat_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3419,c_2086])).

cnf(c_25,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_2096,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3486,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3481,c_2096])).

cnf(c_28821,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_28010,c_3486])).

cnf(c_28822,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_28821])).

cnf(c_36,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k1_relat_1(X0)
    | k6_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f141])).

cnf(c_49,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_674,plain,
    ( ~ v1_relat_1(X0)
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k1_relat_1(X0)
    | k6_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_49])).

cnf(c_675,plain,
    ( ~ v1_relat_1(sK3)
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(sK3)
    | k6_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_674])).

cnf(c_2082,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(sK3)
    | k6_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_675])).

cnf(c_28853,plain,
    ( k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_28822,c_2082])).

cnf(c_29317,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_28853,c_3486])).

cnf(c_29318,plain,
    ( k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_29317])).

cnf(c_43,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_2089,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_4875,plain,
    ( k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_2087,c_2089])).

cnf(c_46,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f142])).

cnf(c_2088,plain,
    ( r1_tarski(k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_5086,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4875,c_2088])).

cnf(c_29354,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_29318,c_5086])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f145])).

cnf(c_2113,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_44,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_659,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_44,c_49])).

cnf(c_660,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0)))
    | ~ r1_tarski(k2_relat_1(sK3),X0)
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_659])).

cnf(c_2083,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_660])).

cnf(c_3639,plain,
    ( v4_relat_1(sK3,k1_relat_1(sK3)) = iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2083,c_2090])).

cnf(c_4120,plain,
    ( r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | v4_relat_1(sK3,k1_relat_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3639,c_3486])).

cnf(c_4121,plain,
    ( v4_relat_1(sK3,k1_relat_1(sK3)) = iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4120])).

cnf(c_4128,plain,
    ( v4_relat_1(sK3,k1_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2113,c_4121])).

cnf(c_29,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_2093,plain,
    ( k7_relat_1(X0,X1) = X0
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4859,plain,
    ( k7_relat_1(sK3,k1_relat_1(sK3)) = sK3
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4128,c_2093])).

cnf(c_7567,plain,
    ( k7_relat_1(sK3,k1_relat_1(sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4859,c_3486])).

cnf(c_27,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_2094,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3814,plain,
    ( k2_relat_1(k7_relat_1(sK3,X0)) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_3486,c_2094])).

cnf(c_7570,plain,
    ( k9_relat_1(sK3,k1_relat_1(sK3)) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_7567,c_3814])).

cnf(c_26,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k9_relat_1(X0,k1_relat_1(X0)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_2095,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k9_relat_1(X0,k1_relat_1(X0))) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_8687,plain,
    ( r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7570,c_2095])).

cnf(c_9276,plain,
    ( r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8687,c_3486])).

cnf(c_29621,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_29354,c_9276])).

cnf(c_32,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f156])).

cnf(c_779,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,X0) = k1_xboole_0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_49])).

cnf(c_780,plain,
    ( r2_hidden(X0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | k1_funct_1(sK3,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_779])).

cnf(c_2076,plain,
    ( k1_funct_1(sK3,X0) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_780])).

cnf(c_29691,plain,
    ( k1_funct_1(sK3,X0) = k1_xboole_0
    | r2_hidden(X0,k1_xboole_0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_29621,c_2076])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_143,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_40,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_2091,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_3337,plain,
    ( k1_funct_1(sK3,X0) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2076,c_2091])).

cnf(c_29690,plain,
    ( k1_funct_1(sK3,X0) = k1_xboole_0
    | r1_tarski(k1_xboole_0,X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_29621,c_3337])).

cnf(c_30034,plain,
    ( k1_funct_1(sK3,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_29691,c_143,c_3486,c_29690])).

cnf(c_30039,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_30034,c_5086])).

cnf(c_3420,plain,
    ( r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),X0)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2083,c_2100])).

cnf(c_4138,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),X0)) = iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3420,c_3486])).

cnf(c_4139,plain,
    ( r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_4138])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2114,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4620,plain,
    ( k2_zfmisc_1(k1_relat_1(sK3),X0) = sK3
    | r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),X0),sK3) != iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4139,c_2114])).

cnf(c_29680,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = sK3
    | r1_tarski(k2_zfmisc_1(k1_xboole_0,X0),sK3) != iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_29621,c_4620])).

cnf(c_5,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f147])).

cnf(c_29745,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_29680,c_5])).

cnf(c_3748,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_5962,plain,
    ( ~ r1_tarski(sK3,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK3)
    | sK3 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3748])).

cnf(c_5964,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK3,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5962])).

cnf(c_5963,plain,
    ( r1_tarski(k1_xboole_0,sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_5966,plain,
    ( r1_tarski(k1_xboole_0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5963])).

cnf(c_29688,plain,
    ( r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_29621,c_4139])).

cnf(c_29723,plain,
    ( r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_29688,c_5])).

cnf(c_30146,plain,
    ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2113,c_29723])).

cnf(c_30160,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_29745,c_5964,c_5966,c_30146])).

cnf(c_30415,plain,
    ( r1_tarski(k9_relat_1(k1_xboole_0,sK2),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_30039,c_30160])).

cnf(c_28,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_30416,plain,
    ( r1_tarski(k1_xboole_0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_30415,c_28])).

cnf(c_2112,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_30418,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_30416,c_2112])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:08:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.34/1.52  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.34/1.52  
% 7.34/1.52  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.34/1.52  
% 7.34/1.52  ------  iProver source info
% 7.34/1.52  
% 7.34/1.52  git: date: 2020-06-30 10:37:57 +0100
% 7.34/1.52  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.34/1.52  git: non_committed_changes: false
% 7.34/1.52  git: last_make_outside_of_git: false
% 7.34/1.52  
% 7.34/1.52  ------ 
% 7.34/1.52  
% 7.34/1.52  ------ Input Options
% 7.34/1.52  
% 7.34/1.52  --out_options                           all
% 7.34/1.52  --tptp_safe_out                         true
% 7.34/1.52  --problem_path                          ""
% 7.34/1.52  --include_path                          ""
% 7.34/1.52  --clausifier                            res/vclausify_rel
% 7.34/1.52  --clausifier_options                    --mode clausify
% 7.34/1.52  --stdin                                 false
% 7.34/1.52  --stats_out                             all
% 7.34/1.52  
% 7.34/1.52  ------ General Options
% 7.34/1.52  
% 7.34/1.52  --fof                                   false
% 7.34/1.52  --time_out_real                         305.
% 7.34/1.52  --time_out_virtual                      -1.
% 7.34/1.52  --symbol_type_check                     false
% 7.34/1.52  --clausify_out                          false
% 7.34/1.52  --sig_cnt_out                           false
% 7.34/1.52  --trig_cnt_out                          false
% 7.34/1.52  --trig_cnt_out_tolerance                1.
% 7.34/1.52  --trig_cnt_out_sk_spl                   false
% 7.34/1.52  --abstr_cl_out                          false
% 7.34/1.52  
% 7.34/1.52  ------ Global Options
% 7.34/1.52  
% 7.34/1.52  --schedule                              default
% 7.34/1.52  --add_important_lit                     false
% 7.34/1.52  --prop_solver_per_cl                    1000
% 7.34/1.52  --min_unsat_core                        false
% 7.34/1.52  --soft_assumptions                      false
% 7.34/1.52  --soft_lemma_size                       3
% 7.34/1.52  --prop_impl_unit_size                   0
% 7.34/1.52  --prop_impl_unit                        []
% 7.34/1.52  --share_sel_clauses                     true
% 7.34/1.52  --reset_solvers                         false
% 7.34/1.52  --bc_imp_inh                            [conj_cone]
% 7.34/1.52  --conj_cone_tolerance                   3.
% 7.34/1.52  --extra_neg_conj                        none
% 7.34/1.52  --large_theory_mode                     true
% 7.34/1.52  --prolific_symb_bound                   200
% 7.34/1.52  --lt_threshold                          2000
% 7.34/1.52  --clause_weak_htbl                      true
% 7.34/1.52  --gc_record_bc_elim                     false
% 7.34/1.52  
% 7.34/1.52  ------ Preprocessing Options
% 7.34/1.52  
% 7.34/1.52  --preprocessing_flag                    true
% 7.34/1.52  --time_out_prep_mult                    0.1
% 7.34/1.52  --splitting_mode                        input
% 7.34/1.52  --splitting_grd                         true
% 7.34/1.52  --splitting_cvd                         false
% 7.34/1.52  --splitting_cvd_svl                     false
% 7.34/1.52  --splitting_nvd                         32
% 7.34/1.52  --sub_typing                            true
% 7.34/1.52  --prep_gs_sim                           true
% 7.34/1.52  --prep_unflatten                        true
% 7.34/1.52  --prep_res_sim                          true
% 7.34/1.52  --prep_upred                            true
% 7.34/1.52  --prep_sem_filter                       exhaustive
% 7.34/1.52  --prep_sem_filter_out                   false
% 7.34/1.52  --pred_elim                             true
% 7.34/1.52  --res_sim_input                         true
% 7.34/1.52  --eq_ax_congr_red                       true
% 7.34/1.52  --pure_diseq_elim                       true
% 7.34/1.52  --brand_transform                       false
% 7.34/1.52  --non_eq_to_eq                          false
% 7.34/1.52  --prep_def_merge                        true
% 7.34/1.52  --prep_def_merge_prop_impl              false
% 7.34/1.52  --prep_def_merge_mbd                    true
% 7.34/1.52  --prep_def_merge_tr_red                 false
% 7.34/1.52  --prep_def_merge_tr_cl                  false
% 7.34/1.52  --smt_preprocessing                     true
% 7.34/1.52  --smt_ac_axioms                         fast
% 7.34/1.52  --preprocessed_out                      false
% 7.34/1.52  --preprocessed_stats                    false
% 7.34/1.52  
% 7.34/1.52  ------ Abstraction refinement Options
% 7.34/1.52  
% 7.34/1.52  --abstr_ref                             []
% 7.34/1.52  --abstr_ref_prep                        false
% 7.34/1.52  --abstr_ref_until_sat                   false
% 7.34/1.52  --abstr_ref_sig_restrict                funpre
% 7.34/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 7.34/1.52  --abstr_ref_under                       []
% 7.34/1.52  
% 7.34/1.52  ------ SAT Options
% 7.34/1.52  
% 7.34/1.52  --sat_mode                              false
% 7.34/1.52  --sat_fm_restart_options                ""
% 7.34/1.52  --sat_gr_def                            false
% 7.34/1.52  --sat_epr_types                         true
% 7.34/1.52  --sat_non_cyclic_types                  false
% 7.34/1.52  --sat_finite_models                     false
% 7.34/1.52  --sat_fm_lemmas                         false
% 7.34/1.52  --sat_fm_prep                           false
% 7.34/1.52  --sat_fm_uc_incr                        true
% 7.34/1.52  --sat_out_model                         small
% 7.34/1.52  --sat_out_clauses                       false
% 7.34/1.52  
% 7.34/1.52  ------ QBF Options
% 7.34/1.52  
% 7.34/1.52  --qbf_mode                              false
% 7.34/1.52  --qbf_elim_univ                         false
% 7.34/1.52  --qbf_dom_inst                          none
% 7.34/1.52  --qbf_dom_pre_inst                      false
% 7.34/1.52  --qbf_sk_in                             false
% 7.34/1.52  --qbf_pred_elim                         true
% 7.34/1.52  --qbf_split                             512
% 7.34/1.52  
% 7.34/1.52  ------ BMC1 Options
% 7.34/1.52  
% 7.34/1.52  --bmc1_incremental                      false
% 7.34/1.52  --bmc1_axioms                           reachable_all
% 7.34/1.52  --bmc1_min_bound                        0
% 7.34/1.52  --bmc1_max_bound                        -1
% 7.34/1.52  --bmc1_max_bound_default                -1
% 7.34/1.52  --bmc1_symbol_reachability              true
% 7.34/1.52  --bmc1_property_lemmas                  false
% 7.34/1.52  --bmc1_k_induction                      false
% 7.34/1.52  --bmc1_non_equiv_states                 false
% 7.34/1.52  --bmc1_deadlock                         false
% 7.34/1.52  --bmc1_ucm                              false
% 7.34/1.52  --bmc1_add_unsat_core                   none
% 7.34/1.52  --bmc1_unsat_core_children              false
% 7.34/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 7.34/1.52  --bmc1_out_stat                         full
% 7.34/1.52  --bmc1_ground_init                      false
% 7.34/1.52  --bmc1_pre_inst_next_state              false
% 7.34/1.52  --bmc1_pre_inst_state                   false
% 7.34/1.52  --bmc1_pre_inst_reach_state             false
% 7.34/1.52  --bmc1_out_unsat_core                   false
% 7.34/1.52  --bmc1_aig_witness_out                  false
% 7.34/1.52  --bmc1_verbose                          false
% 7.34/1.52  --bmc1_dump_clauses_tptp                false
% 7.34/1.52  --bmc1_dump_unsat_core_tptp             false
% 7.34/1.52  --bmc1_dump_file                        -
% 7.34/1.52  --bmc1_ucm_expand_uc_limit              128
% 7.34/1.52  --bmc1_ucm_n_expand_iterations          6
% 7.34/1.52  --bmc1_ucm_extend_mode                  1
% 7.34/1.52  --bmc1_ucm_init_mode                    2
% 7.34/1.52  --bmc1_ucm_cone_mode                    none
% 7.34/1.52  --bmc1_ucm_reduced_relation_type        0
% 7.34/1.52  --bmc1_ucm_relax_model                  4
% 7.34/1.52  --bmc1_ucm_full_tr_after_sat            true
% 7.34/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 7.34/1.52  --bmc1_ucm_layered_model                none
% 7.34/1.52  --bmc1_ucm_max_lemma_size               10
% 7.34/1.52  
% 7.34/1.52  ------ AIG Options
% 7.34/1.52  
% 7.34/1.52  --aig_mode                              false
% 7.34/1.52  
% 7.34/1.52  ------ Instantiation Options
% 7.34/1.52  
% 7.34/1.52  --instantiation_flag                    true
% 7.34/1.52  --inst_sos_flag                         false
% 7.34/1.52  --inst_sos_phase                        true
% 7.34/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.34/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.34/1.52  --inst_lit_sel_side                     num_symb
% 7.34/1.52  --inst_solver_per_active                1400
% 7.34/1.52  --inst_solver_calls_frac                1.
% 7.34/1.52  --inst_passive_queue_type               priority_queues
% 7.34/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.34/1.52  --inst_passive_queues_freq              [25;2]
% 7.34/1.52  --inst_dismatching                      true
% 7.34/1.52  --inst_eager_unprocessed_to_passive     true
% 7.34/1.52  --inst_prop_sim_given                   true
% 7.34/1.52  --inst_prop_sim_new                     false
% 7.34/1.52  --inst_subs_new                         false
% 7.34/1.52  --inst_eq_res_simp                      false
% 7.34/1.52  --inst_subs_given                       false
% 7.34/1.52  --inst_orphan_elimination               true
% 7.34/1.52  --inst_learning_loop_flag               true
% 7.34/1.52  --inst_learning_start                   3000
% 7.34/1.52  --inst_learning_factor                  2
% 7.34/1.52  --inst_start_prop_sim_after_learn       3
% 7.34/1.52  --inst_sel_renew                        solver
% 7.34/1.52  --inst_lit_activity_flag                true
% 7.34/1.52  --inst_restr_to_given                   false
% 7.34/1.52  --inst_activity_threshold               500
% 7.34/1.52  --inst_out_proof                        true
% 7.34/1.52  
% 7.34/1.52  ------ Resolution Options
% 7.34/1.52  
% 7.34/1.52  --resolution_flag                       true
% 7.34/1.52  --res_lit_sel                           adaptive
% 7.34/1.52  --res_lit_sel_side                      none
% 7.34/1.52  --res_ordering                          kbo
% 7.34/1.52  --res_to_prop_solver                    active
% 7.34/1.52  --res_prop_simpl_new                    false
% 7.34/1.52  --res_prop_simpl_given                  true
% 7.34/1.52  --res_passive_queue_type                priority_queues
% 7.34/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.34/1.52  --res_passive_queues_freq               [15;5]
% 7.34/1.52  --res_forward_subs                      full
% 7.34/1.52  --res_backward_subs                     full
% 7.34/1.52  --res_forward_subs_resolution           true
% 7.34/1.52  --res_backward_subs_resolution          true
% 7.34/1.52  --res_orphan_elimination                true
% 7.34/1.52  --res_time_limit                        2.
% 7.34/1.52  --res_out_proof                         true
% 7.34/1.52  
% 7.34/1.52  ------ Superposition Options
% 7.34/1.52  
% 7.34/1.52  --superposition_flag                    true
% 7.34/1.52  --sup_passive_queue_type                priority_queues
% 7.34/1.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.34/1.52  --sup_passive_queues_freq               [8;1;4]
% 7.34/1.52  --demod_completeness_check              fast
% 7.34/1.52  --demod_use_ground                      true
% 7.34/1.52  --sup_to_prop_solver                    passive
% 7.34/1.52  --sup_prop_simpl_new                    true
% 7.34/1.52  --sup_prop_simpl_given                  true
% 7.34/1.52  --sup_fun_splitting                     false
% 7.34/1.52  --sup_smt_interval                      50000
% 7.34/1.52  
% 7.34/1.52  ------ Superposition Simplification Setup
% 7.34/1.52  
% 7.34/1.52  --sup_indices_passive                   []
% 7.34/1.52  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.34/1.52  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.34/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.34/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 7.34/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.34/1.52  --sup_full_bw                           [BwDemod]
% 7.34/1.52  --sup_immed_triv                        [TrivRules]
% 7.34/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.34/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.34/1.52  --sup_immed_bw_main                     []
% 7.34/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.34/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 7.34/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.34/1.52  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.34/1.52  
% 7.34/1.52  ------ Combination Options
% 7.34/1.52  
% 7.34/1.52  --comb_res_mult                         3
% 7.34/1.52  --comb_sup_mult                         2
% 7.34/1.52  --comb_inst_mult                        10
% 7.34/1.52  
% 7.34/1.52  ------ Debug Options
% 7.34/1.52  
% 7.34/1.52  --dbg_backtrace                         false
% 7.34/1.52  --dbg_dump_prop_clauses                 false
% 7.34/1.52  --dbg_dump_prop_clauses_file            -
% 7.34/1.52  --dbg_out_stat                          false
% 7.34/1.52  ------ Parsing...
% 7.34/1.52  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.34/1.52  
% 7.34/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.34/1.52  
% 7.34/1.52  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.34/1.52  
% 7.34/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.34/1.52  ------ Proving...
% 7.34/1.52  ------ Problem Properties 
% 7.34/1.52  
% 7.34/1.52  
% 7.34/1.52  clauses                                 47
% 7.34/1.52  conjectures                             3
% 7.34/1.52  EPR                                     7
% 7.34/1.52  Horn                                    43
% 7.34/1.52  unary                                   22
% 7.34/1.52  binary                                  10
% 7.34/1.52  lits                                    94
% 7.34/1.52  lits eq                                 29
% 7.34/1.52  fd_pure                                 0
% 7.34/1.52  fd_pseudo                               0
% 7.34/1.52  fd_cond                                 1
% 7.34/1.52  fd_pseudo_cond                          4
% 7.34/1.52  AC symbols                              0
% 7.34/1.52  
% 7.34/1.52  ------ Schedule dynamic 5 is on 
% 7.34/1.52  
% 7.34/1.52  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.34/1.52  
% 7.34/1.52  
% 7.34/1.52  ------ 
% 7.34/1.52  Current options:
% 7.34/1.52  ------ 
% 7.34/1.52  
% 7.34/1.52  ------ Input Options
% 7.34/1.52  
% 7.34/1.52  --out_options                           all
% 7.34/1.52  --tptp_safe_out                         true
% 7.34/1.52  --problem_path                          ""
% 7.34/1.52  --include_path                          ""
% 7.34/1.52  --clausifier                            res/vclausify_rel
% 7.34/1.52  --clausifier_options                    --mode clausify
% 7.34/1.52  --stdin                                 false
% 7.34/1.52  --stats_out                             all
% 7.34/1.52  
% 7.34/1.52  ------ General Options
% 7.34/1.52  
% 7.34/1.52  --fof                                   false
% 7.34/1.52  --time_out_real                         305.
% 7.34/1.52  --time_out_virtual                      -1.
% 7.34/1.52  --symbol_type_check                     false
% 7.34/1.52  --clausify_out                          false
% 7.34/1.52  --sig_cnt_out                           false
% 7.34/1.52  --trig_cnt_out                          false
% 7.34/1.52  --trig_cnt_out_tolerance                1.
% 7.34/1.52  --trig_cnt_out_sk_spl                   false
% 7.34/1.52  --abstr_cl_out                          false
% 7.34/1.52  
% 7.34/1.52  ------ Global Options
% 7.34/1.52  
% 7.34/1.52  --schedule                              default
% 7.34/1.52  --add_important_lit                     false
% 7.34/1.52  --prop_solver_per_cl                    1000
% 7.34/1.52  --min_unsat_core                        false
% 7.34/1.52  --soft_assumptions                      false
% 7.34/1.52  --soft_lemma_size                       3
% 7.34/1.52  --prop_impl_unit_size                   0
% 7.34/1.52  --prop_impl_unit                        []
% 7.34/1.52  --share_sel_clauses                     true
% 7.34/1.52  --reset_solvers                         false
% 7.34/1.52  --bc_imp_inh                            [conj_cone]
% 7.34/1.52  --conj_cone_tolerance                   3.
% 7.34/1.52  --extra_neg_conj                        none
% 7.34/1.52  --large_theory_mode                     true
% 7.34/1.52  --prolific_symb_bound                   200
% 7.34/1.52  --lt_threshold                          2000
% 7.34/1.52  --clause_weak_htbl                      true
% 7.34/1.52  --gc_record_bc_elim                     false
% 7.34/1.52  
% 7.34/1.52  ------ Preprocessing Options
% 7.34/1.52  
% 7.34/1.52  --preprocessing_flag                    true
% 7.34/1.52  --time_out_prep_mult                    0.1
% 7.34/1.52  --splitting_mode                        input
% 7.34/1.52  --splitting_grd                         true
% 7.34/1.52  --splitting_cvd                         false
% 7.34/1.52  --splitting_cvd_svl                     false
% 7.34/1.52  --splitting_nvd                         32
% 7.34/1.52  --sub_typing                            true
% 7.34/1.52  --prep_gs_sim                           true
% 7.34/1.52  --prep_unflatten                        true
% 7.34/1.52  --prep_res_sim                          true
% 7.34/1.52  --prep_upred                            true
% 7.34/1.52  --prep_sem_filter                       exhaustive
% 7.34/1.52  --prep_sem_filter_out                   false
% 7.34/1.52  --pred_elim                             true
% 7.34/1.52  --res_sim_input                         true
% 7.34/1.52  --eq_ax_congr_red                       true
% 7.34/1.52  --pure_diseq_elim                       true
% 7.34/1.52  --brand_transform                       false
% 7.34/1.52  --non_eq_to_eq                          false
% 7.34/1.52  --prep_def_merge                        true
% 7.34/1.52  --prep_def_merge_prop_impl              false
% 7.34/1.52  --prep_def_merge_mbd                    true
% 7.34/1.52  --prep_def_merge_tr_red                 false
% 7.34/1.52  --prep_def_merge_tr_cl                  false
% 7.34/1.52  --smt_preprocessing                     true
% 7.34/1.52  --smt_ac_axioms                         fast
% 7.34/1.52  --preprocessed_out                      false
% 7.34/1.52  --preprocessed_stats                    false
% 7.34/1.52  
% 7.34/1.52  ------ Abstraction refinement Options
% 7.34/1.52  
% 7.34/1.52  --abstr_ref                             []
% 7.34/1.52  --abstr_ref_prep                        false
% 7.34/1.52  --abstr_ref_until_sat                   false
% 7.34/1.52  --abstr_ref_sig_restrict                funpre
% 7.34/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 7.34/1.52  --abstr_ref_under                       []
% 7.34/1.52  
% 7.34/1.52  ------ SAT Options
% 7.34/1.52  
% 7.34/1.52  --sat_mode                              false
% 7.34/1.52  --sat_fm_restart_options                ""
% 7.34/1.52  --sat_gr_def                            false
% 7.34/1.52  --sat_epr_types                         true
% 7.34/1.52  --sat_non_cyclic_types                  false
% 7.34/1.52  --sat_finite_models                     false
% 7.34/1.52  --sat_fm_lemmas                         false
% 7.34/1.52  --sat_fm_prep                           false
% 7.34/1.52  --sat_fm_uc_incr                        true
% 7.34/1.52  --sat_out_model                         small
% 7.34/1.52  --sat_out_clauses                       false
% 7.34/1.52  
% 7.34/1.52  ------ QBF Options
% 7.34/1.52  
% 7.34/1.52  --qbf_mode                              false
% 7.34/1.52  --qbf_elim_univ                         false
% 7.34/1.52  --qbf_dom_inst                          none
% 7.34/1.52  --qbf_dom_pre_inst                      false
% 7.34/1.52  --qbf_sk_in                             false
% 7.34/1.52  --qbf_pred_elim                         true
% 7.34/1.52  --qbf_split                             512
% 7.34/1.52  
% 7.34/1.52  ------ BMC1 Options
% 7.34/1.52  
% 7.34/1.52  --bmc1_incremental                      false
% 7.34/1.52  --bmc1_axioms                           reachable_all
% 7.34/1.52  --bmc1_min_bound                        0
% 7.34/1.52  --bmc1_max_bound                        -1
% 7.34/1.52  --bmc1_max_bound_default                -1
% 7.34/1.52  --bmc1_symbol_reachability              true
% 7.34/1.52  --bmc1_property_lemmas                  false
% 7.34/1.52  --bmc1_k_induction                      false
% 7.34/1.52  --bmc1_non_equiv_states                 false
% 7.34/1.52  --bmc1_deadlock                         false
% 7.34/1.52  --bmc1_ucm                              false
% 7.34/1.52  --bmc1_add_unsat_core                   none
% 7.34/1.52  --bmc1_unsat_core_children              false
% 7.34/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 7.34/1.52  --bmc1_out_stat                         full
% 7.34/1.52  --bmc1_ground_init                      false
% 7.34/1.52  --bmc1_pre_inst_next_state              false
% 7.34/1.52  --bmc1_pre_inst_state                   false
% 7.34/1.52  --bmc1_pre_inst_reach_state             false
% 7.34/1.52  --bmc1_out_unsat_core                   false
% 7.34/1.52  --bmc1_aig_witness_out                  false
% 7.34/1.52  --bmc1_verbose                          false
% 7.34/1.52  --bmc1_dump_clauses_tptp                false
% 7.34/1.52  --bmc1_dump_unsat_core_tptp             false
% 7.34/1.52  --bmc1_dump_file                        -
% 7.34/1.52  --bmc1_ucm_expand_uc_limit              128
% 7.34/1.52  --bmc1_ucm_n_expand_iterations          6
% 7.34/1.52  --bmc1_ucm_extend_mode                  1
% 7.34/1.52  --bmc1_ucm_init_mode                    2
% 7.34/1.52  --bmc1_ucm_cone_mode                    none
% 7.34/1.52  --bmc1_ucm_reduced_relation_type        0
% 7.34/1.52  --bmc1_ucm_relax_model                  4
% 7.34/1.52  --bmc1_ucm_full_tr_after_sat            true
% 7.34/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 7.34/1.52  --bmc1_ucm_layered_model                none
% 7.34/1.52  --bmc1_ucm_max_lemma_size               10
% 7.34/1.52  
% 7.34/1.52  ------ AIG Options
% 7.34/1.52  
% 7.34/1.52  --aig_mode                              false
% 7.34/1.52  
% 7.34/1.52  ------ Instantiation Options
% 7.34/1.52  
% 7.34/1.52  --instantiation_flag                    true
% 7.34/1.52  --inst_sos_flag                         false
% 7.34/1.52  --inst_sos_phase                        true
% 7.34/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.34/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.34/1.52  --inst_lit_sel_side                     none
% 7.34/1.52  --inst_solver_per_active                1400
% 7.34/1.52  --inst_solver_calls_frac                1.
% 7.34/1.52  --inst_passive_queue_type               priority_queues
% 7.34/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.34/1.52  --inst_passive_queues_freq              [25;2]
% 7.34/1.52  --inst_dismatching                      true
% 7.34/1.52  --inst_eager_unprocessed_to_passive     true
% 7.34/1.52  --inst_prop_sim_given                   true
% 7.34/1.52  --inst_prop_sim_new                     false
% 7.34/1.52  --inst_subs_new                         false
% 7.34/1.52  --inst_eq_res_simp                      false
% 7.34/1.52  --inst_subs_given                       false
% 7.34/1.52  --inst_orphan_elimination               true
% 7.34/1.52  --inst_learning_loop_flag               true
% 7.34/1.52  --inst_learning_start                   3000
% 7.34/1.52  --inst_learning_factor                  2
% 7.34/1.52  --inst_start_prop_sim_after_learn       3
% 7.34/1.52  --inst_sel_renew                        solver
% 7.34/1.52  --inst_lit_activity_flag                true
% 7.34/1.52  --inst_restr_to_given                   false
% 7.34/1.52  --inst_activity_threshold               500
% 7.34/1.52  --inst_out_proof                        true
% 7.34/1.52  
% 7.34/1.52  ------ Resolution Options
% 7.34/1.52  
% 7.34/1.52  --resolution_flag                       false
% 7.34/1.52  --res_lit_sel                           adaptive
% 7.34/1.52  --res_lit_sel_side                      none
% 7.34/1.52  --res_ordering                          kbo
% 7.34/1.52  --res_to_prop_solver                    active
% 7.34/1.52  --res_prop_simpl_new                    false
% 7.34/1.52  --res_prop_simpl_given                  true
% 7.34/1.52  --res_passive_queue_type                priority_queues
% 7.34/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.34/1.52  --res_passive_queues_freq               [15;5]
% 7.34/1.52  --res_forward_subs                      full
% 7.34/1.52  --res_backward_subs                     full
% 7.34/1.52  --res_forward_subs_resolution           true
% 7.34/1.52  --res_backward_subs_resolution          true
% 7.34/1.52  --res_orphan_elimination                true
% 7.34/1.52  --res_time_limit                        2.
% 7.34/1.52  --res_out_proof                         true
% 7.34/1.52  
% 7.34/1.52  ------ Superposition Options
% 7.34/1.52  
% 7.34/1.52  --superposition_flag                    true
% 7.34/1.52  --sup_passive_queue_type                priority_queues
% 7.34/1.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.34/1.52  --sup_passive_queues_freq               [8;1;4]
% 7.34/1.52  --demod_completeness_check              fast
% 7.34/1.52  --demod_use_ground                      true
% 7.34/1.52  --sup_to_prop_solver                    passive
% 7.34/1.52  --sup_prop_simpl_new                    true
% 7.34/1.52  --sup_prop_simpl_given                  true
% 7.34/1.52  --sup_fun_splitting                     false
% 7.34/1.52  --sup_smt_interval                      50000
% 7.34/1.52  
% 7.34/1.52  ------ Superposition Simplification Setup
% 7.34/1.52  
% 7.34/1.52  --sup_indices_passive                   []
% 7.34/1.52  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.34/1.52  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.34/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.34/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 7.34/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.34/1.52  --sup_full_bw                           [BwDemod]
% 7.34/1.52  --sup_immed_triv                        [TrivRules]
% 7.34/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.34/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.34/1.52  --sup_immed_bw_main                     []
% 7.34/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.34/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 7.34/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.34/1.52  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.34/1.52  
% 7.34/1.52  ------ Combination Options
% 7.34/1.52  
% 7.34/1.52  --comb_res_mult                         3
% 7.34/1.52  --comb_sup_mult                         2
% 7.34/1.52  --comb_inst_mult                        10
% 7.34/1.52  
% 7.34/1.52  ------ Debug Options
% 7.34/1.52  
% 7.34/1.52  --dbg_backtrace                         false
% 7.34/1.52  --dbg_dump_prop_clauses                 false
% 7.34/1.52  --dbg_dump_prop_clauses_file            -
% 7.34/1.52  --dbg_out_stat                          false
% 7.34/1.52  
% 7.34/1.52  
% 7.34/1.52  
% 7.34/1.52  
% 7.34/1.52  ------ Proving...
% 7.34/1.52  
% 7.34/1.52  
% 7.34/1.52  % SZS status Theorem for theBenchmark.p
% 7.34/1.52  
% 7.34/1.52   Resolution empty clause
% 7.34/1.52  
% 7.34/1.52  % SZS output start CNFRefutation for theBenchmark.p
% 7.34/1.52  
% 7.34/1.52  fof(f31,conjecture,(
% 7.34/1.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 7.34/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.34/1.52  
% 7.34/1.52  fof(f32,negated_conjecture,(
% 7.34/1.52    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 7.34/1.52    inference(negated_conjecture,[],[f31])).
% 7.34/1.52  
% 7.34/1.52  fof(f34,plain,(
% 7.34/1.52    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 7.34/1.52    inference(pure_predicate_removal,[],[f32])).
% 7.34/1.52  
% 7.34/1.52  fof(f55,plain,(
% 7.34/1.52    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 7.34/1.52    inference(ennf_transformation,[],[f34])).
% 7.34/1.52  
% 7.34/1.52  fof(f56,plain,(
% 7.34/1.52    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 7.34/1.52    inference(flattening,[],[f55])).
% 7.34/1.52  
% 7.34/1.52  fof(f67,plain,(
% 7.34/1.52    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3))),
% 7.34/1.52    introduced(choice_axiom,[])).
% 7.34/1.52  
% 7.34/1.52  fof(f68,plain,(
% 7.34/1.52    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3)),
% 7.34/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f56,f67])).
% 7.34/1.52  
% 7.34/1.52  fof(f123,plain,(
% 7.34/1.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 7.34/1.52    inference(cnf_transformation,[],[f68])).
% 7.34/1.52  
% 7.34/1.52  fof(f3,axiom,(
% 7.34/1.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.34/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.34/1.52  
% 7.34/1.52  fof(f73,plain,(
% 7.34/1.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.34/1.52    inference(cnf_transformation,[],[f3])).
% 7.34/1.52  
% 7.34/1.52  fof(f4,axiom,(
% 7.34/1.52    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.34/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.34/1.52  
% 7.34/1.52  fof(f74,plain,(
% 7.34/1.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.34/1.52    inference(cnf_transformation,[],[f4])).
% 7.34/1.52  
% 7.34/1.52  fof(f5,axiom,(
% 7.34/1.52    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.34/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.34/1.52  
% 7.34/1.52  fof(f75,plain,(
% 7.34/1.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.34/1.52    inference(cnf_transformation,[],[f5])).
% 7.34/1.52  
% 7.34/1.52  fof(f6,axiom,(
% 7.34/1.52    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.34/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.34/1.52  
% 7.34/1.52  fof(f76,plain,(
% 7.34/1.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.34/1.52    inference(cnf_transformation,[],[f6])).
% 7.34/1.52  
% 7.34/1.52  fof(f7,axiom,(
% 7.34/1.52    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.34/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.34/1.52  
% 7.34/1.52  fof(f77,plain,(
% 7.34/1.52    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.34/1.52    inference(cnf_transformation,[],[f7])).
% 7.34/1.52  
% 7.34/1.52  fof(f8,axiom,(
% 7.34/1.52    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 7.34/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.34/1.52  
% 7.34/1.52  fof(f78,plain,(
% 7.34/1.52    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 7.34/1.52    inference(cnf_transformation,[],[f8])).
% 7.34/1.52  
% 7.34/1.52  fof(f9,axiom,(
% 7.34/1.52    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 7.34/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.34/1.52  
% 7.34/1.52  fof(f79,plain,(
% 7.34/1.52    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 7.34/1.52    inference(cnf_transformation,[],[f9])).
% 7.34/1.52  
% 7.34/1.52  fof(f126,plain,(
% 7.34/1.52    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 7.34/1.52    inference(definition_unfolding,[],[f78,f79])).
% 7.34/1.52  
% 7.34/1.52  fof(f127,plain,(
% 7.34/1.52    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 7.34/1.52    inference(definition_unfolding,[],[f77,f126])).
% 7.34/1.52  
% 7.34/1.52  fof(f128,plain,(
% 7.34/1.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 7.34/1.52    inference(definition_unfolding,[],[f76,f127])).
% 7.34/1.52  
% 7.34/1.52  fof(f129,plain,(
% 7.34/1.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 7.34/1.52    inference(definition_unfolding,[],[f75,f128])).
% 7.34/1.52  
% 7.34/1.52  fof(f130,plain,(
% 7.34/1.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 7.34/1.52    inference(definition_unfolding,[],[f74,f129])).
% 7.34/1.52  
% 7.34/1.52  fof(f131,plain,(
% 7.34/1.52    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 7.34/1.52    inference(definition_unfolding,[],[f73,f130])).
% 7.34/1.52  
% 7.34/1.52  fof(f143,plain,(
% 7.34/1.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))),
% 7.34/1.52    inference(definition_unfolding,[],[f123,f131])).
% 7.34/1.52  
% 7.34/1.52  fof(f28,axiom,(
% 7.34/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.34/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.34/1.52  
% 7.34/1.52  fof(f51,plain,(
% 7.34/1.52    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.34/1.52    inference(ennf_transformation,[],[f28])).
% 7.34/1.52  
% 7.34/1.52  fof(f117,plain,(
% 7.34/1.52    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.34/1.52    inference(cnf_transformation,[],[f51])).
% 7.34/1.52  
% 7.34/1.52  fof(f16,axiom,(
% 7.34/1.52    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 7.34/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.34/1.52  
% 7.34/1.52  fof(f40,plain,(
% 7.34/1.52    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.34/1.52    inference(ennf_transformation,[],[f16])).
% 7.34/1.52  
% 7.34/1.52  fof(f64,plain,(
% 7.34/1.52    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.34/1.52    inference(nnf_transformation,[],[f40])).
% 7.34/1.52  
% 7.34/1.52  fof(f97,plain,(
% 7.34/1.52    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.34/1.52    inference(cnf_transformation,[],[f64])).
% 7.34/1.52  
% 7.34/1.52  fof(f11,axiom,(
% 7.34/1.52    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> ~(k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3))),
% 7.34/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.34/1.52  
% 7.34/1.52  fof(f36,plain,(
% 7.34/1.52    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3))),
% 7.34/1.52    inference(ennf_transformation,[],[f11])).
% 7.34/1.52  
% 7.34/1.52  fof(f61,plain,(
% 7.34/1.52    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & ((k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3) | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 7.34/1.52    inference(nnf_transformation,[],[f36])).
% 7.34/1.52  
% 7.34/1.52  fof(f62,plain,(
% 7.34/1.52    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 7.34/1.52    inference(flattening,[],[f61])).
% 7.34/1.52  
% 7.34/1.52  fof(f83,plain,(
% 7.34/1.52    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))) )),
% 7.34/1.52    inference(cnf_transformation,[],[f62])).
% 7.34/1.52  
% 7.34/1.52  fof(f140,plain,(
% 7.34/1.52    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = X3 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2) = X3 | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = X3 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = X3 | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = X3 | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X3 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))) )),
% 7.34/1.52    inference(definition_unfolding,[],[f83,f129,f130,f130,f130,f131,f131,f131,f129])).
% 7.34/1.52  
% 7.34/1.52  fof(f13,axiom,(
% 7.34/1.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.34/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.34/1.52  
% 7.34/1.52  fof(f63,plain,(
% 7.34/1.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.34/1.52    inference(nnf_transformation,[],[f13])).
% 7.34/1.52  
% 7.34/1.52  fof(f93,plain,(
% 7.34/1.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.34/1.52    inference(cnf_transformation,[],[f63])).
% 7.34/1.52  
% 7.34/1.52  fof(f15,axiom,(
% 7.34/1.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.34/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.34/1.52  
% 7.34/1.52  fof(f39,plain,(
% 7.34/1.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.34/1.52    inference(ennf_transformation,[],[f15])).
% 7.34/1.52  
% 7.34/1.52  fof(f96,plain,(
% 7.34/1.52    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.34/1.52    inference(cnf_transformation,[],[f39])).
% 7.34/1.52  
% 7.34/1.52  fof(f94,plain,(
% 7.34/1.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.34/1.52    inference(cnf_transformation,[],[f63])).
% 7.34/1.52  
% 7.34/1.52  fof(f18,axiom,(
% 7.34/1.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.34/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.34/1.52  
% 7.34/1.52  fof(f101,plain,(
% 7.34/1.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.34/1.52    inference(cnf_transformation,[],[f18])).
% 7.34/1.52  
% 7.34/1.52  fof(f25,axiom,(
% 7.34/1.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 7.34/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.34/1.52  
% 7.34/1.52  fof(f48,plain,(
% 7.34/1.52    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.34/1.52    inference(ennf_transformation,[],[f25])).
% 7.34/1.52  
% 7.34/1.52  fof(f49,plain,(
% 7.34/1.52    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.34/1.52    inference(flattening,[],[f48])).
% 7.34/1.52  
% 7.34/1.52  fof(f112,plain,(
% 7.34/1.52    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.34/1.52    inference(cnf_transformation,[],[f49])).
% 7.34/1.52  
% 7.34/1.52  fof(f141,plain,(
% 7.34/1.52    ( ! [X0,X1] : (k6_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.34/1.52    inference(definition_unfolding,[],[f112,f131,f131])).
% 7.34/1.52  
% 7.34/1.52  fof(f122,plain,(
% 7.34/1.52    v1_funct_1(sK3)),
% 7.34/1.52    inference(cnf_transformation,[],[f68])).
% 7.34/1.52  
% 7.34/1.52  fof(f29,axiom,(
% 7.34/1.52    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 7.34/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.34/1.52  
% 7.34/1.52  fof(f52,plain,(
% 7.34/1.52    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.34/1.52    inference(ennf_transformation,[],[f29])).
% 7.34/1.52  
% 7.34/1.52  fof(f119,plain,(
% 7.34/1.52    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.34/1.52    inference(cnf_transformation,[],[f52])).
% 7.34/1.52  
% 7.34/1.52  fof(f125,plain,(
% 7.34/1.52    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 7.34/1.52    inference(cnf_transformation,[],[f68])).
% 7.34/1.52  
% 7.34/1.52  fof(f142,plain,(
% 7.34/1.52    ~r1_tarski(k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 7.34/1.52    inference(definition_unfolding,[],[f125,f131,f131])).
% 7.34/1.52  
% 7.34/1.52  fof(f1,axiom,(
% 7.34/1.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.34/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.34/1.52  
% 7.34/1.52  fof(f57,plain,(
% 7.34/1.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.34/1.52    inference(nnf_transformation,[],[f1])).
% 7.34/1.52  
% 7.34/1.52  fof(f58,plain,(
% 7.34/1.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.34/1.52    inference(flattening,[],[f57])).
% 7.34/1.52  
% 7.34/1.52  fof(f69,plain,(
% 7.34/1.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.34/1.52    inference(cnf_transformation,[],[f58])).
% 7.34/1.52  
% 7.34/1.52  fof(f145,plain,(
% 7.34/1.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.34/1.52    inference(equality_resolution,[],[f69])).
% 7.34/1.52  
% 7.34/1.52  fof(f30,axiom,(
% 7.34/1.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 7.34/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.34/1.52  
% 7.34/1.52  fof(f33,plain,(
% 7.34/1.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_1(X1))))),
% 7.34/1.52    inference(pure_predicate_removal,[],[f30])).
% 7.34/1.52  
% 7.34/1.52  fof(f53,plain,(
% 7.34/1.52    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.34/1.52    inference(ennf_transformation,[],[f33])).
% 7.34/1.52  
% 7.34/1.52  fof(f54,plain,(
% 7.34/1.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.34/1.52    inference(flattening,[],[f53])).
% 7.34/1.52  
% 7.34/1.52  fof(f121,plain,(
% 7.34/1.52    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.34/1.52    inference(cnf_transformation,[],[f54])).
% 7.34/1.52  
% 7.34/1.52  fof(f22,axiom,(
% 7.34/1.52    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 7.34/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.34/1.52  
% 7.34/1.52  fof(f44,plain,(
% 7.34/1.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.34/1.52    inference(ennf_transformation,[],[f22])).
% 7.34/1.52  
% 7.34/1.52  fof(f45,plain,(
% 7.34/1.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.34/1.52    inference(flattening,[],[f44])).
% 7.34/1.52  
% 7.34/1.52  fof(f105,plain,(
% 7.34/1.52    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.34/1.52    inference(cnf_transformation,[],[f45])).
% 7.34/1.52  
% 7.34/1.52  fof(f20,axiom,(
% 7.34/1.52    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 7.34/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.34/1.52  
% 7.34/1.52  fof(f43,plain,(
% 7.34/1.52    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.34/1.52    inference(ennf_transformation,[],[f20])).
% 7.34/1.52  
% 7.34/1.52  fof(f103,plain,(
% 7.34/1.52    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.34/1.52    inference(cnf_transformation,[],[f43])).
% 7.34/1.52  
% 7.34/1.52  fof(f19,axiom,(
% 7.34/1.52    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))))),
% 7.34/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.34/1.52  
% 7.34/1.52  fof(f42,plain,(
% 7.34/1.52    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 7.34/1.52    inference(ennf_transformation,[],[f19])).
% 7.34/1.52  
% 7.34/1.52  fof(f102,plain,(
% 7.34/1.52    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))) | ~v1_relat_1(X1)) )),
% 7.34/1.52    inference(cnf_transformation,[],[f42])).
% 7.34/1.52  
% 7.34/1.52  fof(f24,axiom,(
% 7.34/1.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 7.34/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.34/1.52  
% 7.34/1.52  fof(f46,plain,(
% 7.34/1.52    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.34/1.52    inference(ennf_transformation,[],[f24])).
% 7.34/1.52  
% 7.34/1.52  fof(f47,plain,(
% 7.34/1.52    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.34/1.52    inference(flattening,[],[f46])).
% 7.34/1.52  
% 7.34/1.52  fof(f66,plain,(
% 7.34/1.52    ! [X0] : (! [X1,X2] : ((((k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2)) | r2_hidden(X1,k1_relat_1(X0))) & (((k1_funct_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(X1,X2),X0)) & (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.34/1.52    inference(nnf_transformation,[],[f47])).
% 7.34/1.52  
% 7.34/1.52  fof(f111,plain,(
% 7.34/1.52    ( ! [X2,X0,X1] : (k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2 | r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.34/1.52    inference(cnf_transformation,[],[f66])).
% 7.34/1.52  
% 7.34/1.52  fof(f156,plain,(
% 7.34/1.52    ( ! [X0,X1] : (k1_xboole_0 = k1_funct_1(X0,X1) | r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.34/1.52    inference(equality_resolution,[],[f111])).
% 7.34/1.52  
% 7.34/1.52  fof(f2,axiom,(
% 7.34/1.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.34/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.34/1.52  
% 7.34/1.52  fof(f72,plain,(
% 7.34/1.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.34/1.52    inference(cnf_transformation,[],[f2])).
% 7.34/1.52  
% 7.34/1.52  fof(f27,axiom,(
% 7.34/1.52    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 7.34/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.34/1.52  
% 7.34/1.52  fof(f50,plain,(
% 7.34/1.52    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 7.34/1.52    inference(ennf_transformation,[],[f27])).
% 7.34/1.52  
% 7.34/1.52  fof(f116,plain,(
% 7.34/1.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 7.34/1.52    inference(cnf_transformation,[],[f50])).
% 7.34/1.52  
% 7.34/1.52  fof(f71,plain,(
% 7.34/1.52    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.34/1.52    inference(cnf_transformation,[],[f58])).
% 7.34/1.52  
% 7.34/1.52  fof(f10,axiom,(
% 7.34/1.52    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.34/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.34/1.52  
% 7.34/1.52  fof(f59,plain,(
% 7.34/1.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.34/1.52    inference(nnf_transformation,[],[f10])).
% 7.34/1.52  
% 7.34/1.52  fof(f60,plain,(
% 7.34/1.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.34/1.52    inference(flattening,[],[f59])).
% 7.34/1.52  
% 7.34/1.52  fof(f81,plain,(
% 7.34/1.52    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 7.34/1.52    inference(cnf_transformation,[],[f60])).
% 7.34/1.52  
% 7.34/1.52  fof(f147,plain,(
% 7.34/1.52    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 7.34/1.52    inference(equality_resolution,[],[f81])).
% 7.34/1.52  
% 7.34/1.52  fof(f21,axiom,(
% 7.34/1.52    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 7.34/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.34/1.52  
% 7.34/1.52  fof(f104,plain,(
% 7.34/1.52    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 7.34/1.52    inference(cnf_transformation,[],[f21])).
% 7.34/1.52  
% 7.34/1.52  cnf(c_48,negated_conjecture,
% 7.34/1.52      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) ),
% 7.34/1.52      inference(cnf_transformation,[],[f143]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_2087,plain,
% 7.34/1.52      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
% 7.34/1.52      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_42,plain,
% 7.34/1.52      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.34/1.52      inference(cnf_transformation,[],[f117]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_2090,plain,
% 7.34/1.52      ( v4_relat_1(X0,X1) = iProver_top
% 7.34/1.52      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 7.34/1.52      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_3638,plain,
% 7.34/1.52      ( v4_relat_1(sK3,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
% 7.34/1.52      inference(superposition,[status(thm)],[c_2087,c_2090]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_22,plain,
% 7.34/1.52      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 7.34/1.52      inference(cnf_transformation,[],[f97]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_2097,plain,
% 7.34/1.52      ( v4_relat_1(X0,X1) != iProver_top
% 7.34/1.52      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 7.34/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.34/1.52      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_15,plain,
% 7.34/1.52      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))
% 7.34/1.52      | k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3) = X0
% 7.34/1.52      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3) = X0
% 7.34/1.52      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3) = X0
% 7.34/1.52      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = X0
% 7.34/1.52      | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) = X0
% 7.34/1.52      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = X0
% 7.34/1.52      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
% 7.34/1.52      | k1_xboole_0 = X0 ),
% 7.34/1.52      inference(cnf_transformation,[],[f140]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_2103,plain,
% 7.34/1.52      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = X3
% 7.34/1.52      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2) = X3
% 7.34/1.52      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = X3
% 7.34/1.52      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = X3
% 7.34/1.52      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = X3
% 7.34/1.52      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X3
% 7.34/1.52      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X3
% 7.34/1.52      | k1_xboole_0 = X3
% 7.34/1.52      | r1_tarski(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) != iProver_top ),
% 7.34/1.52      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_9679,plain,
% 7.34/1.52      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_relat_1(X1)
% 7.34/1.52      | k6_enumset1(X0,X0,X0,X0,X0,X0,X2,X3) = k1_relat_1(X1)
% 7.34/1.52      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X3) = k1_relat_1(X1)
% 7.34/1.52      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3) = k1_relat_1(X1)
% 7.34/1.52      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2) = k1_relat_1(X1)
% 7.34/1.52      | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) = k1_relat_1(X1)
% 7.34/1.52      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = k1_relat_1(X1)
% 7.34/1.52      | k1_relat_1(X1) = k1_xboole_0
% 7.34/1.52      | v4_relat_1(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X2,X3)) != iProver_top
% 7.34/1.52      | v1_relat_1(X1) != iProver_top ),
% 7.34/1.52      inference(superposition,[status(thm)],[c_2097,c_2103]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_28010,plain,
% 7.34/1.52      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
% 7.34/1.52      | k1_relat_1(sK3) = k1_xboole_0
% 7.34/1.52      | v1_relat_1(sK3) != iProver_top ),
% 7.34/1.52      inference(superposition,[status(thm)],[c_3638,c_9679]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_18,plain,
% 7.34/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.34/1.52      inference(cnf_transformation,[],[f93]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_2100,plain,
% 7.34/1.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.34/1.52      | r1_tarski(X0,X1) = iProver_top ),
% 7.34/1.52      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_3419,plain,
% 7.34/1.52      ( r1_tarski(sK3,k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) = iProver_top ),
% 7.34/1.52      inference(superposition,[status(thm)],[c_2087,c_2100]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_20,plain,
% 7.34/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 7.34/1.52      inference(cnf_transformation,[],[f96]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_17,plain,
% 7.34/1.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.34/1.52      inference(cnf_transformation,[],[f94]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_331,plain,
% 7.34/1.52      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.34/1.52      inference(prop_impl,[status(thm)],[c_17]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_332,plain,
% 7.34/1.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.34/1.52      inference(renaming,[status(thm)],[c_331]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_407,plain,
% 7.34/1.52      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 7.34/1.52      inference(bin_hyper_res,[status(thm)],[c_20,c_332]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_2086,plain,
% 7.34/1.52      ( r1_tarski(X0,X1) != iProver_top
% 7.34/1.52      | v1_relat_1(X1) != iProver_top
% 7.34/1.52      | v1_relat_1(X0) = iProver_top ),
% 7.34/1.52      inference(predicate_to_equality,[status(thm)],[c_407]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_3481,plain,
% 7.34/1.52      ( v1_relat_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != iProver_top
% 7.34/1.52      | v1_relat_1(sK3) = iProver_top ),
% 7.34/1.52      inference(superposition,[status(thm)],[c_3419,c_2086]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_25,plain,
% 7.34/1.52      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.34/1.52      inference(cnf_transformation,[],[f101]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_2096,plain,
% 7.34/1.52      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 7.34/1.52      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_3486,plain,
% 7.34/1.52      ( v1_relat_1(sK3) = iProver_top ),
% 7.34/1.52      inference(forward_subsumption_resolution,[status(thm)],[c_3481,c_2096]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_28821,plain,
% 7.34/1.52      ( k1_relat_1(sK3) = k1_xboole_0
% 7.34/1.52      | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(sK3) ),
% 7.34/1.52      inference(global_propositional_subsumption,
% 7.34/1.52                [status(thm)],
% 7.34/1.52                [c_28010,c_3486]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_28822,plain,
% 7.34/1.52      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
% 7.34/1.52      | k1_relat_1(sK3) = k1_xboole_0 ),
% 7.34/1.52      inference(renaming,[status(thm)],[c_28821]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_36,plain,
% 7.34/1.52      ( ~ v1_funct_1(X0)
% 7.34/1.52      | ~ v1_relat_1(X0)
% 7.34/1.52      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k1_relat_1(X0)
% 7.34/1.52      | k6_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
% 7.34/1.52      inference(cnf_transformation,[],[f141]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_49,negated_conjecture,
% 7.34/1.52      ( v1_funct_1(sK3) ),
% 7.34/1.52      inference(cnf_transformation,[],[f122]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_674,plain,
% 7.34/1.52      ( ~ v1_relat_1(X0)
% 7.34/1.52      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k1_relat_1(X0)
% 7.34/1.52      | k6_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
% 7.34/1.52      | sK3 != X0 ),
% 7.34/1.52      inference(resolution_lifted,[status(thm)],[c_36,c_49]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_675,plain,
% 7.34/1.52      ( ~ v1_relat_1(sK3)
% 7.34/1.52      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(sK3)
% 7.34/1.52      | k6_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
% 7.34/1.52      inference(unflattening,[status(thm)],[c_674]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_2082,plain,
% 7.34/1.52      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(sK3)
% 7.34/1.52      | k6_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
% 7.34/1.52      | v1_relat_1(sK3) != iProver_top ),
% 7.34/1.52      inference(predicate_to_equality,[status(thm)],[c_675]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_28853,plain,
% 7.34/1.52      ( k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
% 7.34/1.52      | k1_relat_1(sK3) = k1_xboole_0
% 7.34/1.52      | v1_relat_1(sK3) != iProver_top ),
% 7.34/1.52      inference(superposition,[status(thm)],[c_28822,c_2082]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_29317,plain,
% 7.34/1.52      ( k1_relat_1(sK3) = k1_xboole_0
% 7.34/1.52      | k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) ),
% 7.34/1.52      inference(global_propositional_subsumption,
% 7.34/1.52                [status(thm)],
% 7.34/1.52                [c_28853,c_3486]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_29318,plain,
% 7.34/1.52      ( k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
% 7.34/1.52      | k1_relat_1(sK3) = k1_xboole_0 ),
% 7.34/1.52      inference(renaming,[status(thm)],[c_29317]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_43,plain,
% 7.34/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.34/1.52      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 7.34/1.52      inference(cnf_transformation,[],[f119]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_2089,plain,
% 7.34/1.52      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 7.34/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.34/1.52      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_4875,plain,
% 7.34/1.52      ( k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
% 7.34/1.52      inference(superposition,[status(thm)],[c_2087,c_2089]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_46,negated_conjecture,
% 7.34/1.52      ( ~ r1_tarski(k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
% 7.34/1.52      inference(cnf_transformation,[],[f142]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_2088,plain,
% 7.34/1.52      ( r1_tarski(k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 7.34/1.52      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_5086,plain,
% 7.34/1.52      ( r1_tarski(k9_relat_1(sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 7.34/1.52      inference(demodulation,[status(thm)],[c_4875,c_2088]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_29354,plain,
% 7.34/1.52      ( k1_relat_1(sK3) = k1_xboole_0
% 7.34/1.52      | r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) != iProver_top ),
% 7.34/1.52      inference(superposition,[status(thm)],[c_29318,c_5086]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_2,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f145]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_2113,plain,
% 7.34/1.52      ( r1_tarski(X0,X0) = iProver_top ),
% 7.34/1.52      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_44,plain,
% 7.34/1.52      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 7.34/1.52      | ~ r1_tarski(k2_relat_1(X0),X1)
% 7.34/1.52      | ~ v1_funct_1(X0)
% 7.34/1.52      | ~ v1_relat_1(X0) ),
% 7.34/1.52      inference(cnf_transformation,[],[f121]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_659,plain,
% 7.34/1.52      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 7.34/1.52      | ~ r1_tarski(k2_relat_1(X0),X1)
% 7.34/1.52      | ~ v1_relat_1(X0)
% 7.34/1.52      | sK3 != X0 ),
% 7.34/1.52      inference(resolution_lifted,[status(thm)],[c_44,c_49]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_660,plain,
% 7.34/1.52      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0)))
% 7.34/1.52      | ~ r1_tarski(k2_relat_1(sK3),X0)
% 7.34/1.52      | ~ v1_relat_1(sK3) ),
% 7.34/1.52      inference(unflattening,[status(thm)],[c_659]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_2083,plain,
% 7.34/1.52      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) = iProver_top
% 7.34/1.52      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 7.34/1.52      | v1_relat_1(sK3) != iProver_top ),
% 7.34/1.52      inference(predicate_to_equality,[status(thm)],[c_660]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_3639,plain,
% 7.34/1.52      ( v4_relat_1(sK3,k1_relat_1(sK3)) = iProver_top
% 7.34/1.52      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 7.34/1.52      | v1_relat_1(sK3) != iProver_top ),
% 7.34/1.52      inference(superposition,[status(thm)],[c_2083,c_2090]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_4120,plain,
% 7.34/1.52      ( r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 7.34/1.52      | v4_relat_1(sK3,k1_relat_1(sK3)) = iProver_top ),
% 7.34/1.52      inference(global_propositional_subsumption,[status(thm)],[c_3639,c_3486]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_4121,plain,
% 7.34/1.52      ( v4_relat_1(sK3,k1_relat_1(sK3)) = iProver_top
% 7.34/1.52      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
% 7.34/1.52      inference(renaming,[status(thm)],[c_4120]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_4128,plain,
% 7.34/1.52      ( v4_relat_1(sK3,k1_relat_1(sK3)) = iProver_top ),
% 7.34/1.52      inference(superposition,[status(thm)],[c_2113,c_4121]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_29,plain,
% 7.34/1.52      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 7.34/1.52      inference(cnf_transformation,[],[f105]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_2093,plain,
% 7.34/1.52      ( k7_relat_1(X0,X1) = X0
% 7.34/1.52      | v4_relat_1(X0,X1) != iProver_top
% 7.34/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.34/1.52      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_4859,plain,
% 7.34/1.52      ( k7_relat_1(sK3,k1_relat_1(sK3)) = sK3
% 7.34/1.52      | v1_relat_1(sK3) != iProver_top ),
% 7.34/1.52      inference(superposition,[status(thm)],[c_4128,c_2093]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_7567,plain,
% 7.34/1.52      ( k7_relat_1(sK3,k1_relat_1(sK3)) = sK3 ),
% 7.34/1.52      inference(global_propositional_subsumption,[status(thm)],[c_4859,c_3486]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_27,plain,
% 7.34/1.52      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 7.34/1.52      inference(cnf_transformation,[],[f103]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_2094,plain,
% 7.34/1.52      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 7.34/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.34/1.52      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_3814,plain,
% 7.34/1.52      ( k2_relat_1(k7_relat_1(sK3,X0)) = k9_relat_1(sK3,X0) ),
% 7.34/1.52      inference(superposition,[status(thm)],[c_3486,c_2094]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_7570,plain,
% 7.34/1.52      ( k9_relat_1(sK3,k1_relat_1(sK3)) = k2_relat_1(sK3) ),
% 7.34/1.52      inference(superposition,[status(thm)],[c_7567,c_3814]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_26,plain,
% 7.34/1.52      ( r1_tarski(k9_relat_1(X0,X1),k9_relat_1(X0,k1_relat_1(X0)))
% 7.34/1.52      | ~ v1_relat_1(X0) ),
% 7.34/1.52      inference(cnf_transformation,[],[f102]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_2095,plain,
% 7.34/1.52      ( r1_tarski(k9_relat_1(X0,X1),k9_relat_1(X0,k1_relat_1(X0))) = iProver_top
% 7.34/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.34/1.52      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_8687,plain,
% 7.34/1.52      ( r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3)) = iProver_top
% 7.34/1.52      | v1_relat_1(sK3) != iProver_top ),
% 7.34/1.52      inference(superposition,[status(thm)],[c_7570,c_2095]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_9276,plain,
% 7.34/1.52      ( r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3)) = iProver_top ),
% 7.34/1.52      inference(global_propositional_subsumption,[status(thm)],[c_8687,c_3486]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_29621,plain,
% 7.34/1.52      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 7.34/1.52      inference(forward_subsumption_resolution,[status(thm)],[c_29354,c_9276]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_32,plain,
% 7.34/1.52      ( r2_hidden(X0,k1_relat_1(X1))
% 7.34/1.52      | ~ v1_funct_1(X1)
% 7.34/1.52      | ~ v1_relat_1(X1)
% 7.34/1.52      | k1_funct_1(X1,X0) = k1_xboole_0 ),
% 7.34/1.52      inference(cnf_transformation,[],[f156]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_779,plain,
% 7.34/1.52      ( r2_hidden(X0,k1_relat_1(X1))
% 7.34/1.52      | ~ v1_relat_1(X1)
% 7.34/1.52      | k1_funct_1(X1,X0) = k1_xboole_0
% 7.34/1.52      | sK3 != X1 ),
% 7.34/1.52      inference(resolution_lifted,[status(thm)],[c_32,c_49]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_780,plain,
% 7.34/1.52      ( r2_hidden(X0,k1_relat_1(sK3))
% 7.34/1.52      | ~ v1_relat_1(sK3)
% 7.34/1.52      | k1_funct_1(sK3,X0) = k1_xboole_0 ),
% 7.34/1.52      inference(unflattening,[status(thm)],[c_779]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_2076,plain,
% 7.34/1.52      ( k1_funct_1(sK3,X0) = k1_xboole_0
% 7.34/1.52      | r2_hidden(X0,k1_relat_1(sK3)) = iProver_top
% 7.34/1.52      | v1_relat_1(sK3) != iProver_top ),
% 7.34/1.52      inference(predicate_to_equality,[status(thm)],[c_780]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_29691,plain,
% 7.34/1.52      ( k1_funct_1(sK3,X0) = k1_xboole_0
% 7.34/1.52      | r2_hidden(X0,k1_xboole_0) = iProver_top
% 7.34/1.52      | v1_relat_1(sK3) != iProver_top ),
% 7.34/1.52      inference(demodulation,[status(thm)],[c_29621,c_2076]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_3,plain,
% 7.34/1.52      ( r1_tarski(k1_xboole_0,X0) ),
% 7.34/1.52      inference(cnf_transformation,[],[f72]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_143,plain,
% 7.34/1.52      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.34/1.52      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_40,plain,
% 7.34/1.52      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 7.34/1.52      inference(cnf_transformation,[],[f116]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_2091,plain,
% 7.34/1.52      ( r2_hidden(X0,X1) != iProver_top | r1_tarski(X1,X0) != iProver_top ),
% 7.34/1.52      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_3337,plain,
% 7.34/1.52      ( k1_funct_1(sK3,X0) = k1_xboole_0
% 7.34/1.52      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 7.34/1.52      | v1_relat_1(sK3) != iProver_top ),
% 7.34/1.52      inference(superposition,[status(thm)],[c_2076,c_2091]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_29690,plain,
% 7.34/1.52      ( k1_funct_1(sK3,X0) = k1_xboole_0
% 7.34/1.52      | r1_tarski(k1_xboole_0,X0) != iProver_top
% 7.34/1.52      | v1_relat_1(sK3) != iProver_top ),
% 7.34/1.52      inference(demodulation,[status(thm)],[c_29621,c_3337]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_30034,plain,
% 7.34/1.52      ( k1_funct_1(sK3,X0) = k1_xboole_0 ),
% 7.34/1.52      inference(global_propositional_subsumption,
% 7.34/1.52                [status(thm)],
% 7.34/1.52                [c_29691,c_143,c_3486,c_29690]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_30039,plain,
% 7.34/1.52      ( r1_tarski(k9_relat_1(sK3,sK2),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 7.34/1.52      inference(demodulation,[status(thm)],[c_30034,c_5086]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_3420,plain,
% 7.34/1.52      ( r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 7.34/1.52      | r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),X0)) = iProver_top
% 7.34/1.52      | v1_relat_1(sK3) != iProver_top ),
% 7.34/1.52      inference(superposition,[status(thm)],[c_2083,c_2100]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_4138,plain,
% 7.34/1.52      ( r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),X0)) = iProver_top
% 7.34/1.52      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
% 7.34/1.52      inference(global_propositional_subsumption,[status(thm)],[c_3420,c_3486]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_4139,plain,
% 7.34/1.52      ( r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 7.34/1.52      | r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),X0)) = iProver_top ),
% 7.34/1.52      inference(renaming,[status(thm)],[c_4138]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_0,plain,
% 7.34/1.52      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.34/1.52      inference(cnf_transformation,[],[f71]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_2114,plain,
% 7.34/1.52      ( X0 = X1
% 7.34/1.52      | r1_tarski(X1,X0) != iProver_top
% 7.34/1.52      | r1_tarski(X0,X1) != iProver_top ),
% 7.34/1.52      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_4620,plain,
% 7.34/1.52      ( k2_zfmisc_1(k1_relat_1(sK3),X0) = sK3
% 7.34/1.52      | r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),X0),sK3) != iProver_top
% 7.34/1.52      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
% 7.34/1.52      inference(superposition,[status(thm)],[c_4139,c_2114]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_29680,plain,
% 7.34/1.52      ( k2_zfmisc_1(k1_xboole_0,X0) = sK3
% 7.34/1.52      | r1_tarski(k2_zfmisc_1(k1_xboole_0,X0),sK3) != iProver_top
% 7.34/1.52      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
% 7.34/1.52      inference(demodulation,[status(thm)],[c_29621,c_4620]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_5,plain,
% 7.34/1.52      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.34/1.52      inference(cnf_transformation,[],[f147]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_29745,plain,
% 7.34/1.52      ( sK3 = k1_xboole_0
% 7.34/1.52      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 7.34/1.52      | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 7.34/1.52      inference(light_normalisation,[status(thm)],[c_29680,c_5]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_3748,plain,
% 7.34/1.52      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK3,X0) | sK3 = X0 ),
% 7.34/1.52      inference(instantiation,[status(thm)],[c_0]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_5962,plain,
% 7.34/1.52      ( ~ r1_tarski(sK3,k1_xboole_0)
% 7.34/1.52      | ~ r1_tarski(k1_xboole_0,sK3)
% 7.34/1.52      | sK3 = k1_xboole_0 ),
% 7.34/1.52      inference(instantiation,[status(thm)],[c_3748]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_5964,plain,
% 7.34/1.52      ( sK3 = k1_xboole_0
% 7.34/1.52      | r1_tarski(sK3,k1_xboole_0) != iProver_top
% 7.34/1.52      | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 7.34/1.52      inference(predicate_to_equality,[status(thm)],[c_5962]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_5963,plain,
% 7.34/1.52      ( r1_tarski(k1_xboole_0,sK3) ),
% 7.34/1.52      inference(instantiation,[status(thm)],[c_3]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_5966,plain,
% 7.34/1.52      ( r1_tarski(k1_xboole_0,sK3) = iProver_top ),
% 7.34/1.52      inference(predicate_to_equality,[status(thm)],[c_5963]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_29688,plain,
% 7.34/1.52      ( r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 7.34/1.52      | r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,X0)) = iProver_top ),
% 7.34/1.52      inference(demodulation,[status(thm)],[c_29621,c_4139]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_29723,plain,
% 7.34/1.52      ( r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 7.34/1.52      | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 7.34/1.52      inference(light_normalisation,[status(thm)],[c_29688,c_5]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_30146,plain,
% 7.34/1.52      ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 7.34/1.52      inference(superposition,[status(thm)],[c_2113,c_29723]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_30160,plain,
% 7.34/1.52      ( sK3 = k1_xboole_0 ),
% 7.34/1.52      inference(global_propositional_subsumption,
% 7.34/1.52                [status(thm)],
% 7.34/1.52                [c_29745,c_5964,c_5966,c_30146]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_30415,plain,
% 7.34/1.52      ( r1_tarski(k9_relat_1(k1_xboole_0,sK2),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 7.34/1.52      inference(light_normalisation,[status(thm)],[c_30039,c_30160]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_28,plain,
% 7.34/1.52      ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.34/1.52      inference(cnf_transformation,[],[f104]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_30416,plain,
% 7.34/1.52      ( r1_tarski(k1_xboole_0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 7.34/1.52      inference(demodulation,[status(thm)],[c_30415,c_28]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_2112,plain,
% 7.34/1.52      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.34/1.52      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.34/1.52  
% 7.34/1.52  cnf(c_30418,plain,
% 7.34/1.52      ( $false ),
% 7.34/1.52      inference(forward_subsumption_resolution,[status(thm)],[c_30416,c_2112]) ).
% 7.34/1.52  
% 7.34/1.52  
% 7.34/1.52  % SZS output end CNFRefutation for theBenchmark.p
% 7.34/1.52  
% 7.34/1.52  ------                               Statistics
% 7.34/1.52  
% 7.34/1.52  ------ General
% 7.34/1.52  
% 7.34/1.52  abstr_ref_over_cycles:                  0
% 7.34/1.52  abstr_ref_under_cycles:                 0
% 7.34/1.52  gc_basic_clause_elim:                   0
% 7.34/1.52  forced_gc_time:                         0
% 7.34/1.52  parsing_time:                           0.009
% 7.34/1.52  unif_index_cands_time:                  0.
% 7.34/1.52  unif_index_add_time:                    0.
% 7.34/1.52  orderings_time:                         0.
% 7.34/1.52  out_proof_time:                         0.017
% 7.34/1.52  total_time:                             0.82
% 7.34/1.52  num_of_symbols:                         53
% 7.34/1.52  num_of_terms:                           24398
% 7.34/1.52  
% 7.34/1.52  ------ Preprocessing
% 7.34/1.52  
% 7.34/1.52  num_of_splits:                          0
% 7.34/1.52  num_of_split_atoms:                     0
% 7.34/1.52  num_of_reused_defs:                     0
% 7.34/1.52  num_eq_ax_congr_red:                    16
% 7.34/1.52  num_of_sem_filtered_clauses:            1
% 7.34/1.52  num_of_subtypes:                        0
% 7.34/1.52  monotx_restored_types:                  0
% 7.34/1.52  sat_num_of_epr_types:                   0
% 7.34/1.52  sat_num_of_non_cyclic_types:            0
% 7.34/1.52  sat_guarded_non_collapsed_types:        0
% 7.34/1.52  num_pure_diseq_elim:                    0
% 7.34/1.52  simp_replaced_by:                       0
% 7.34/1.52  res_preprocessed:                       219
% 7.34/1.52  prep_upred:                             0
% 7.34/1.52  prep_unflattend:                        12
% 7.34/1.52  smt_new_axioms:                         0
% 7.34/1.52  pred_elim_cands:                        5
% 7.34/1.52  pred_elim:                              2
% 7.34/1.52  pred_elim_cl:                           0
% 7.34/1.52  pred_elim_cycles:                       5
% 7.34/1.52  merged_defs:                            8
% 7.34/1.52  merged_defs_ncl:                        0
% 7.34/1.52  bin_hyper_res:                          9
% 7.34/1.52  prep_cycles:                            4
% 7.34/1.52  pred_elim_time:                         0.008
% 7.34/1.52  splitting_time:                         0.
% 7.34/1.52  sem_filter_time:                        0.
% 7.34/1.52  monotx_time:                            0.001
% 7.34/1.52  subtype_inf_time:                       0.
% 7.34/1.52  
% 7.34/1.52  ------ Problem properties
% 7.34/1.52  
% 7.34/1.52  clauses:                                47
% 7.34/1.52  conjectures:                            3
% 7.34/1.52  epr:                                    7
% 7.34/1.52  horn:                                   43
% 7.34/1.52  ground:                                 6
% 7.34/1.52  unary:                                  22
% 7.34/1.52  binary:                                 10
% 7.34/1.52  lits:                                   94
% 7.34/1.52  lits_eq:                                29
% 7.34/1.52  fd_pure:                                0
% 7.34/1.52  fd_pseudo:                              0
% 7.34/1.52  fd_cond:                                1
% 7.34/1.52  fd_pseudo_cond:                         4
% 7.34/1.52  ac_symbols:                             0
% 7.34/1.52  
% 7.34/1.52  ------ Propositional Solver
% 7.34/1.52  
% 7.34/1.52  prop_solver_calls:                      29
% 7.34/1.52  prop_fast_solver_calls:                 1949
% 7.34/1.52  smt_solver_calls:                       0
% 7.34/1.52  smt_fast_solver_calls:                  0
% 7.34/1.52  prop_num_of_clauses:                    11533
% 7.34/1.52  prop_preprocess_simplified:             23127
% 7.34/1.52  prop_fo_subsumed:                       82
% 7.34/1.52  prop_solver_time:                       0.
% 7.34/1.52  smt_solver_time:                        0.
% 7.34/1.52  smt_fast_solver_time:                   0.
% 7.34/1.52  prop_fast_solver_time:                  0.
% 7.34/1.52  prop_unsat_core_time:                   0.
% 7.34/1.52  
% 7.34/1.52  ------ QBF
% 7.34/1.52  
% 7.34/1.52  qbf_q_res:                              0
% 7.34/1.52  qbf_num_tautologies:                    0
% 7.34/1.52  qbf_prep_cycles:                        0
% 7.34/1.52  
% 7.34/1.52  ------ BMC1
% 7.34/1.52  
% 7.34/1.52  bmc1_current_bound:                     -1
% 7.34/1.52  bmc1_last_solved_bound:                 -1
% 7.34/1.52  bmc1_unsat_core_size:                   -1
% 7.34/1.52  bmc1_unsat_core_parents_size:           -1
% 7.34/1.52  bmc1_merge_next_fun:                    0
% 7.34/1.52  bmc1_unsat_core_clauses_time:           0.
% 7.34/1.52  
% 7.34/1.52  ------ Instantiation
% 7.34/1.52  
% 7.34/1.52  inst_num_of_clauses:                    2908
% 7.34/1.52  inst_num_in_passive:                    743
% 7.34/1.52  inst_num_in_active:                     1321
% 7.34/1.52  inst_num_in_unprocessed:                846
% 7.34/1.52  inst_num_of_loops:                      1420
% 7.34/1.52  inst_num_of_learning_restarts:          0
% 7.34/1.52  inst_num_moves_active_passive:          89
% 7.34/1.52  inst_lit_activity:                      0
% 7.34/1.52  inst_lit_activity_moves:                0
% 7.34/1.52  inst_num_tautologies:                   0
% 7.34/1.52  inst_num_prop_implied:                  0
% 7.34/1.52  inst_num_existing_simplified:           0
% 7.34/1.52  inst_num_eq_res_simplified:             0
% 7.34/1.52  inst_num_child_elim:                    0
% 7.34/1.52  inst_num_of_dismatching_blockings:      1824
% 7.34/1.52  inst_num_of_non_proper_insts:           3864
% 7.34/1.52  inst_num_of_duplicates:                 0
% 7.34/1.52  inst_inst_num_from_inst_to_res:         0
% 7.34/1.52  inst_dismatching_checking_time:         0.
% 7.34/1.52  
% 7.34/1.52  ------ Resolution
% 7.34/1.52  
% 7.34/1.52  res_num_of_clauses:                     0
% 7.34/1.52  res_num_in_passive:                     0
% 7.34/1.52  res_num_in_active:                      0
% 7.34/1.52  res_num_of_loops:                       223
% 7.34/1.52  res_forward_subset_subsumed:            544
% 7.34/1.52  res_backward_subset_subsumed:           26
% 7.34/1.52  res_forward_subsumed:                   1
% 7.34/1.52  res_backward_subsumed:                  0
% 7.34/1.52  res_forward_subsumption_resolution:     0
% 7.34/1.52  res_backward_subsumption_resolution:    0
% 7.34/1.52  res_clause_to_clause_subsumption:       2594
% 7.34/1.52  res_orphan_elimination:                 0
% 7.34/1.52  res_tautology_del:                      155
% 7.34/1.52  res_num_eq_res_simplified:              0
% 7.34/1.52  res_num_sel_changes:                    0
% 7.34/1.52  res_moves_from_active_to_pass:          0
% 7.34/1.52  
% 7.34/1.52  ------ Superposition
% 7.34/1.52  
% 7.34/1.52  sup_time_total:                         0.
% 7.34/1.52  sup_time_generating:                    0.
% 7.34/1.52  sup_time_sim_full:                      0.
% 7.34/1.52  sup_time_sim_immed:                     0.
% 7.34/1.52  
% 7.34/1.52  sup_num_of_clauses:                     456
% 7.34/1.52  sup_num_in_active:                      131
% 7.34/1.52  sup_num_in_passive:                     325
% 7.34/1.52  sup_num_of_loops:                       283
% 7.34/1.52  sup_fw_superposition:                   678
% 7.34/1.52  sup_bw_superposition:                   452
% 7.34/1.52  sup_immediate_simplified:               391
% 7.34/1.52  sup_given_eliminated:                   3
% 7.34/1.52  comparisons_done:                       0
% 7.34/1.52  comparisons_avoided:                    33
% 7.34/1.52  
% 7.34/1.52  ------ Simplifications
% 7.34/1.52  
% 7.34/1.52  
% 7.34/1.52  sim_fw_subset_subsumed:                 115
% 7.34/1.52  sim_bw_subset_subsumed:                 59
% 7.34/1.52  sim_fw_subsumed:                        111
% 7.34/1.52  sim_bw_subsumed:                        16
% 7.34/1.52  sim_fw_subsumption_res:                 4
% 7.34/1.52  sim_bw_subsumption_res:                 0
% 7.34/1.52  sim_tautology_del:                      30
% 7.34/1.52  sim_eq_tautology_del:                   140
% 7.34/1.52  sim_eq_res_simp:                        0
% 7.34/1.52  sim_fw_demodulated:                     74
% 7.34/1.52  sim_bw_demodulated:                     120
% 7.34/1.52  sim_light_normalised:                   166
% 7.34/1.52  sim_joinable_taut:                      0
% 7.34/1.52  sim_joinable_simp:                      0
% 7.34/1.52  sim_ac_normalised:                      0
% 7.34/1.52  sim_smt_subsumption:                    0
% 7.34/1.52  
%------------------------------------------------------------------------------
