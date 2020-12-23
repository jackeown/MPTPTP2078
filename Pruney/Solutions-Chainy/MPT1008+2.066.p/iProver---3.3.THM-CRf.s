%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:18 EST 2020

% Result     : Theorem 2.85s
% Output     : CNFRefutation 2.85s
% Verified   : 
% Statistics : Number of formulae       :  197 ( 853 expanded)
%              Number of clauses        :   99 ( 209 expanded)
%              Number of leaves         :   29 ( 213 expanded)
%              Depth                    :   23
%              Number of atoms          :  420 (2069 expanded)
%              Number of equality atoms :  258 (1138 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f20])).

fof(f14,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f104,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f69,f59])).

fof(f19,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f98,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f56,f59])).

fof(f5,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f58,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f96,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f55,f59])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f70,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f73,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f19])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f94,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f62,f63])).

fof(f95,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f61,f94])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f64,f95])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k1_tarski(X0)))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k1_tarski(X0)))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k1_tarski(X0)))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f105,plain,(
    ! [X0,X1] :
      ( k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k2_enumset1(X0,X0,X0,X0)))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f76,f95,f95])).

fof(f28,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    inference(negated_conjecture,[],[f28])).

fof(f48,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f49,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f48])).

fof(f52,plain,
    ( ? [X0,X1,X2] :
        ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( k1_tarski(k1_funct_1(sK2,sK0)) != k2_relset_1(k1_tarski(sK0),sK1,sK2)
      & k1_xboole_0 != sK1
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_2(sK2,k1_tarski(sK0),sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( k1_tarski(k1_funct_1(sK2,sK0)) != k2_relset_1(k1_tarski(sK0),sK1,sK2)
    & k1_xboole_0 != sK1
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_2(sK2,k1_tarski(sK0),sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f49,f52])).

fof(f89,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f91,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f53])).

fof(f107,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f91,f95])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f93,plain,(
    k1_tarski(k1_funct_1(sK2,sK0)) != k2_relset_1(k1_tarski(sK0),sK1,sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f106,plain,(
    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) ),
    inference(definition_unfolding,[],[f93,f95,f95])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f90,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f108,plain,(
    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f90,f95])).

fof(f27,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
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
    inference(ennf_transformation,[],[f27])).

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

fof(f51,plain,(
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
    inference(nnf_transformation,[],[f47])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f92,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f53])).

fof(f25,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f23])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f54,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f30])).

fof(f97,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f54,f59])).

fof(f4,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f99,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f57,f59])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f65,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f102,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) != k2_enumset1(X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f65,f95,f95,f95])).

fof(f109,plain,(
    ! [X1] : k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)) != k2_enumset1(X1,X1,X1,X1) ),
    inference(equality_resolution,[],[f102])).

cnf(c_17,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_10,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1200,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2242,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_1200])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k4_xboole_0(k2_relat_1(X0),k4_xboole_0(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1199,plain,
    ( k10_relat_1(X0,k4_xboole_0(k2_relat_1(X0),k4_xboole_0(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3566,plain,
    ( k10_relat_1(k1_xboole_0,k4_xboole_0(k2_relat_1(k1_xboole_0),k4_xboole_0(k2_relat_1(k1_xboole_0),X0))) = k10_relat_1(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_2242,c_1199])).

cnf(c_15,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_310,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2
    | k1_xboole_0 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_4])).

cnf(c_311,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(unflattening,[status(thm)],[c_310])).

cnf(c_1371,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_311,c_311])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1688,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_311,c_0])).

cnf(c_5,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1702,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1688,c_5])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1198,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3476,plain,
    ( k10_relat_1(k1_xboole_0,k2_relat_1(k1_xboole_0)) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2242,c_1198])).

cnf(c_16,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_3478,plain,
    ( k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3476,c_15,c_16])).

cnf(c_3568,plain,
    ( k10_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3566,c_15,c_1371,c_1702,c_3478])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_13,plain,
    ( ~ r1_xboole_0(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k7_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_317,plain,
    ( r2_hidden(X0,X1)
    | ~ v1_relat_1(X2)
    | k2_enumset1(X0,X0,X0,X0) != X3
    | k7_relat_1(X2,X3) = k1_xboole_0
    | k1_relat_1(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_13])).

cnf(c_318,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k7_relat_1(X1,k2_enumset1(X0,X0,X0,X0)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_317])).

cnf(c_1197,plain,
    ( k7_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_318])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k2_enumset1(X0,X0,X0,X0))) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_356,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k2_enumset1(X0,X0,X0,X0)))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_35])).

cnf(c_357,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | k2_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)) = k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0,X0,X0,X0))) ),
    inference(unflattening,[status(thm)],[c_356])).

cnf(c_1196,plain,
    ( k2_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)) = k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0,X0,X0,X0)))
    | r2_hidden(X0,k1_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_357])).

cnf(c_358,plain,
    ( k2_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)) = k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0,X0,X0,X0)))
    | r2_hidden(X0,k1_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_357])).

cnf(c_1039,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1307,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) = k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_1039])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_589,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_33])).

cnf(c_590,plain,
    ( v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_589])).

cnf(c_1313,plain,
    ( v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_590])).

cnf(c_1314,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1313])).

cnf(c_1989,plain,
    ( r2_hidden(X0,k1_relat_1(sK2)) != iProver_top
    | k2_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)) = k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0,X0,X0,X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1196,c_358,c_1307,c_1314])).

cnf(c_1990,plain,
    ( k2_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)) = k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0,X0,X0,X0)))
    | r2_hidden(X0,k1_relat_1(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1989])).

cnf(c_2095,plain,
    ( k2_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)) = k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0,X0,X0,X0)))
    | k7_relat_1(sK2,k2_enumset1(X0,X0,X0,X0)) = k1_xboole_0
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1197,c_1990])).

cnf(c_2111,plain,
    ( ~ v1_relat_1(sK2)
    | k2_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)) = k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0,X0,X0,X0)))
    | k7_relat_1(sK2,k2_enumset1(X0,X0,X0,X0)) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2095])).

cnf(c_2451,plain,
    ( k7_relat_1(sK2,k2_enumset1(X0,X0,X0,X0)) = k1_xboole_0
    | k2_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)) = k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0,X0,X0,X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2095,c_1307,c_1313,c_2111])).

cnf(c_2452,plain,
    ( k2_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)) = k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0,X0,X0,X0)))
    | k7_relat_1(sK2,k2_enumset1(X0,X0,X0,X0)) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2451])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_580,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_33])).

cnf(c_581,plain,
    ( k2_relset_1(X0,X1,sK2) = k2_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_580])).

cnf(c_1322,plain,
    ( k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2) ),
    inference(equality_resolution,[status(thm)],[c_581])).

cnf(c_31,negated_conjecture,
    ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1464,plain,
    ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1322,c_31])).

cnf(c_2461,plain,
    ( k7_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) = k1_xboole_0
    | k2_relat_1(k7_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0))) != k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2452,c_1464])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_562,plain,
    ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_33])).

cnf(c_563,plain,
    ( k8_relset_1(X0,X1,sK2,X1) = k1_relset_1(X0,X1,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_562])).

cnf(c_1356,plain,
    ( k8_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2,sK1) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) ),
    inference(equality_resolution,[status(thm)],[c_563])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_517,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_33])).

cnf(c_518,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | k1_relset_1(X0,X1,sK2) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_517])).

cnf(c_811,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != X0
    | k1_relset_1(X0,X1,sK2) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK1 != X1
    | sK2 != sK2
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_518])).

cnf(c_812,plain,
    ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_811])).

cnf(c_32,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_813,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_812,c_32])).

cnf(c_814,plain,
    ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    inference(renaming,[status(thm)],[c_813])).

cnf(c_869,plain,
    ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(equality_resolution_simp,[status(thm)],[c_814])).

cnf(c_1505,plain,
    ( k8_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2,sK1) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(light_normalisation,[status(thm)],[c_1356,c_869])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_571,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_33])).

cnf(c_572,plain,
    ( k8_relset_1(X0,X1,sK2,X2) = k10_relat_1(sK2,X2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_571])).

cnf(c_1343,plain,
    ( k8_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(equality_resolution,[status(thm)],[c_572])).

cnf(c_1506,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k10_relat_1(sK2,sK1) ),
    inference(demodulation,[status(thm)],[c_1505,c_1343])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_14,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_336,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_20,c_14])).

cnf(c_340,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_336,c_20,c_19,c_14])).

cnf(c_508,plain,
    ( k7_relat_1(X0,X1) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_340,c_33])).

cnf(c_509,plain,
    ( k7_relat_1(sK2,X0) = sK2
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_508])).

cnf(c_1319,plain,
    ( k7_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) = sK2 ),
    inference(equality_resolution,[status(thm)],[c_509])).

cnf(c_1511,plain,
    ( k7_relat_1(sK2,k10_relat_1(sK2,sK1)) = sK2 ),
    inference(demodulation,[status(thm)],[c_1506,c_1319])).

cnf(c_2464,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | sK2 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2461,c_1506,c_1511])).

cnf(c_2465,plain,
    ( sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_2464])).

cnf(c_2506,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k10_relat_1(k1_xboole_0,sK1) ),
    inference(demodulation,[status(thm)],[c_2465,c_1506])).

cnf(c_3575,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3568,c_2506])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1686,plain,
    ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1687,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3,c_0])).

cnf(c_1705,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1687,c_5])).

cnf(c_1690,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_3,c_0])).

cnf(c_1696,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1690,c_3])).

cnf(c_1706,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1705,c_1696])).

cnf(c_1710,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1686,c_1706])).

cnf(c_8,plain,
    ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)) != k2_enumset1(X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_3792,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1710,c_8])).

cnf(c_4170,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3575,c_3792])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:48:08 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.85/0.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.85/0.97  
% 2.85/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.85/0.97  
% 2.85/0.97  ------  iProver source info
% 2.85/0.97  
% 2.85/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.85/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.85/0.97  git: non_committed_changes: false
% 2.85/0.97  git: last_make_outside_of_git: false
% 2.85/0.97  
% 2.85/0.97  ------ 
% 2.85/0.97  
% 2.85/0.97  ------ Input Options
% 2.85/0.97  
% 2.85/0.97  --out_options                           all
% 2.85/0.97  --tptp_safe_out                         true
% 2.85/0.97  --problem_path                          ""
% 2.85/0.97  --include_path                          ""
% 2.85/0.97  --clausifier                            res/vclausify_rel
% 2.85/0.97  --clausifier_options                    --mode clausify
% 2.85/0.97  --stdin                                 false
% 2.85/0.97  --stats_out                             all
% 2.85/0.97  
% 2.85/0.97  ------ General Options
% 2.85/0.97  
% 2.85/0.97  --fof                                   false
% 2.85/0.97  --time_out_real                         305.
% 2.85/0.97  --time_out_virtual                      -1.
% 2.85/0.97  --symbol_type_check                     false
% 2.85/0.97  --clausify_out                          false
% 2.85/0.97  --sig_cnt_out                           false
% 2.85/0.97  --trig_cnt_out                          false
% 2.85/0.97  --trig_cnt_out_tolerance                1.
% 2.85/0.97  --trig_cnt_out_sk_spl                   false
% 2.85/0.97  --abstr_cl_out                          false
% 2.85/0.97  
% 2.85/0.97  ------ Global Options
% 2.85/0.97  
% 2.85/0.97  --schedule                              default
% 2.85/0.97  --add_important_lit                     false
% 2.85/0.97  --prop_solver_per_cl                    1000
% 2.85/0.97  --min_unsat_core                        false
% 2.85/0.97  --soft_assumptions                      false
% 2.85/0.97  --soft_lemma_size                       3
% 2.85/0.97  --prop_impl_unit_size                   0
% 2.85/0.97  --prop_impl_unit                        []
% 2.85/0.97  --share_sel_clauses                     true
% 2.85/0.97  --reset_solvers                         false
% 2.85/0.97  --bc_imp_inh                            [conj_cone]
% 2.85/0.97  --conj_cone_tolerance                   3.
% 2.85/0.97  --extra_neg_conj                        none
% 2.85/0.97  --large_theory_mode                     true
% 2.85/0.97  --prolific_symb_bound                   200
% 2.85/0.97  --lt_threshold                          2000
% 2.85/0.97  --clause_weak_htbl                      true
% 2.85/0.97  --gc_record_bc_elim                     false
% 2.85/0.97  
% 2.85/0.97  ------ Preprocessing Options
% 2.85/0.97  
% 2.85/0.97  --preprocessing_flag                    true
% 2.85/0.97  --time_out_prep_mult                    0.1
% 2.85/0.97  --splitting_mode                        input
% 2.85/0.97  --splitting_grd                         true
% 2.85/0.97  --splitting_cvd                         false
% 2.85/0.97  --splitting_cvd_svl                     false
% 2.85/0.97  --splitting_nvd                         32
% 2.85/0.97  --sub_typing                            true
% 2.85/0.97  --prep_gs_sim                           true
% 2.85/0.97  --prep_unflatten                        true
% 2.85/0.97  --prep_res_sim                          true
% 2.85/0.97  --prep_upred                            true
% 2.85/0.97  --prep_sem_filter                       exhaustive
% 2.85/0.97  --prep_sem_filter_out                   false
% 2.85/0.97  --pred_elim                             true
% 2.85/0.97  --res_sim_input                         true
% 2.85/0.97  --eq_ax_congr_red                       true
% 2.85/0.97  --pure_diseq_elim                       true
% 2.85/0.97  --brand_transform                       false
% 2.85/0.97  --non_eq_to_eq                          false
% 2.85/0.97  --prep_def_merge                        true
% 2.85/0.97  --prep_def_merge_prop_impl              false
% 2.85/0.97  --prep_def_merge_mbd                    true
% 2.85/0.97  --prep_def_merge_tr_red                 false
% 2.85/0.97  --prep_def_merge_tr_cl                  false
% 2.85/0.97  --smt_preprocessing                     true
% 2.85/0.97  --smt_ac_axioms                         fast
% 2.85/0.97  --preprocessed_out                      false
% 2.85/0.97  --preprocessed_stats                    false
% 2.85/0.97  
% 2.85/0.97  ------ Abstraction refinement Options
% 2.85/0.97  
% 2.85/0.97  --abstr_ref                             []
% 2.85/0.97  --abstr_ref_prep                        false
% 2.85/0.97  --abstr_ref_until_sat                   false
% 2.85/0.97  --abstr_ref_sig_restrict                funpre
% 2.85/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.85/0.97  --abstr_ref_under                       []
% 2.85/0.97  
% 2.85/0.97  ------ SAT Options
% 2.85/0.97  
% 2.85/0.97  --sat_mode                              false
% 2.85/0.97  --sat_fm_restart_options                ""
% 2.85/0.97  --sat_gr_def                            false
% 2.85/0.97  --sat_epr_types                         true
% 2.85/0.97  --sat_non_cyclic_types                  false
% 2.85/0.97  --sat_finite_models                     false
% 2.85/0.97  --sat_fm_lemmas                         false
% 2.85/0.97  --sat_fm_prep                           false
% 2.85/0.97  --sat_fm_uc_incr                        true
% 2.85/0.97  --sat_out_model                         small
% 2.85/0.97  --sat_out_clauses                       false
% 2.85/0.97  
% 2.85/0.97  ------ QBF Options
% 2.85/0.97  
% 2.85/0.97  --qbf_mode                              false
% 2.85/0.97  --qbf_elim_univ                         false
% 2.85/0.97  --qbf_dom_inst                          none
% 2.85/0.97  --qbf_dom_pre_inst                      false
% 2.85/0.97  --qbf_sk_in                             false
% 2.85/0.97  --qbf_pred_elim                         true
% 2.85/0.97  --qbf_split                             512
% 2.85/0.97  
% 2.85/0.97  ------ BMC1 Options
% 2.85/0.97  
% 2.85/0.97  --bmc1_incremental                      false
% 2.85/0.97  --bmc1_axioms                           reachable_all
% 2.85/0.97  --bmc1_min_bound                        0
% 2.85/0.97  --bmc1_max_bound                        -1
% 2.85/0.97  --bmc1_max_bound_default                -1
% 2.85/0.97  --bmc1_symbol_reachability              true
% 2.85/0.97  --bmc1_property_lemmas                  false
% 2.85/0.97  --bmc1_k_induction                      false
% 2.85/0.97  --bmc1_non_equiv_states                 false
% 2.85/0.97  --bmc1_deadlock                         false
% 2.85/0.97  --bmc1_ucm                              false
% 2.85/0.97  --bmc1_add_unsat_core                   none
% 2.85/0.97  --bmc1_unsat_core_children              false
% 2.85/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.85/0.97  --bmc1_out_stat                         full
% 2.85/0.97  --bmc1_ground_init                      false
% 2.85/0.97  --bmc1_pre_inst_next_state              false
% 2.85/0.97  --bmc1_pre_inst_state                   false
% 2.85/0.97  --bmc1_pre_inst_reach_state             false
% 2.85/0.97  --bmc1_out_unsat_core                   false
% 2.85/0.97  --bmc1_aig_witness_out                  false
% 2.85/0.97  --bmc1_verbose                          false
% 2.85/0.97  --bmc1_dump_clauses_tptp                false
% 2.85/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.85/0.97  --bmc1_dump_file                        -
% 2.85/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.85/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.85/0.97  --bmc1_ucm_extend_mode                  1
% 2.85/0.97  --bmc1_ucm_init_mode                    2
% 2.85/0.97  --bmc1_ucm_cone_mode                    none
% 2.85/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.85/0.97  --bmc1_ucm_relax_model                  4
% 2.85/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.85/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.85/0.97  --bmc1_ucm_layered_model                none
% 2.85/0.97  --bmc1_ucm_max_lemma_size               10
% 2.85/0.97  
% 2.85/0.97  ------ AIG Options
% 2.85/0.97  
% 2.85/0.97  --aig_mode                              false
% 2.85/0.97  
% 2.85/0.97  ------ Instantiation Options
% 2.85/0.97  
% 2.85/0.97  --instantiation_flag                    true
% 2.85/0.97  --inst_sos_flag                         false
% 2.85/0.97  --inst_sos_phase                        true
% 2.85/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.85/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.85/0.97  --inst_lit_sel_side                     num_symb
% 2.85/0.97  --inst_solver_per_active                1400
% 2.85/0.97  --inst_solver_calls_frac                1.
% 2.85/0.97  --inst_passive_queue_type               priority_queues
% 2.85/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.85/0.97  --inst_passive_queues_freq              [25;2]
% 2.85/0.97  --inst_dismatching                      true
% 2.85/0.97  --inst_eager_unprocessed_to_passive     true
% 2.85/0.97  --inst_prop_sim_given                   true
% 2.85/0.97  --inst_prop_sim_new                     false
% 2.85/0.97  --inst_subs_new                         false
% 2.85/0.97  --inst_eq_res_simp                      false
% 2.85/0.97  --inst_subs_given                       false
% 2.85/0.97  --inst_orphan_elimination               true
% 2.85/0.97  --inst_learning_loop_flag               true
% 2.85/0.97  --inst_learning_start                   3000
% 2.85/0.97  --inst_learning_factor                  2
% 2.85/0.97  --inst_start_prop_sim_after_learn       3
% 2.85/0.97  --inst_sel_renew                        solver
% 2.85/0.97  --inst_lit_activity_flag                true
% 2.85/0.97  --inst_restr_to_given                   false
% 2.85/0.97  --inst_activity_threshold               500
% 2.85/0.97  --inst_out_proof                        true
% 2.85/0.97  
% 2.85/0.97  ------ Resolution Options
% 2.85/0.97  
% 2.85/0.97  --resolution_flag                       true
% 2.85/0.97  --res_lit_sel                           adaptive
% 2.85/0.97  --res_lit_sel_side                      none
% 2.85/0.97  --res_ordering                          kbo
% 2.85/0.97  --res_to_prop_solver                    active
% 2.85/0.97  --res_prop_simpl_new                    false
% 2.85/0.97  --res_prop_simpl_given                  true
% 2.85/0.97  --res_passive_queue_type                priority_queues
% 2.85/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.85/0.97  --res_passive_queues_freq               [15;5]
% 2.85/0.97  --res_forward_subs                      full
% 2.85/0.97  --res_backward_subs                     full
% 2.85/0.97  --res_forward_subs_resolution           true
% 2.85/0.97  --res_backward_subs_resolution          true
% 2.85/0.97  --res_orphan_elimination                true
% 2.85/0.97  --res_time_limit                        2.
% 2.85/0.97  --res_out_proof                         true
% 2.85/0.97  
% 2.85/0.97  ------ Superposition Options
% 2.85/0.97  
% 2.85/0.97  --superposition_flag                    true
% 2.85/0.97  --sup_passive_queue_type                priority_queues
% 2.85/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.85/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.85/0.97  --demod_completeness_check              fast
% 2.85/0.97  --demod_use_ground                      true
% 2.85/0.97  --sup_to_prop_solver                    passive
% 2.85/0.97  --sup_prop_simpl_new                    true
% 2.85/0.97  --sup_prop_simpl_given                  true
% 2.85/0.97  --sup_fun_splitting                     false
% 2.85/0.97  --sup_smt_interval                      50000
% 2.85/0.97  
% 2.85/0.97  ------ Superposition Simplification Setup
% 2.85/0.97  
% 2.85/0.97  --sup_indices_passive                   []
% 2.85/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.85/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.85/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.85/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.85/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.85/0.97  --sup_full_bw                           [BwDemod]
% 2.85/0.97  --sup_immed_triv                        [TrivRules]
% 2.85/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.85/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.85/0.97  --sup_immed_bw_main                     []
% 2.85/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.85/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.85/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.85/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.85/0.97  
% 2.85/0.97  ------ Combination Options
% 2.85/0.97  
% 2.85/0.97  --comb_res_mult                         3
% 2.85/0.97  --comb_sup_mult                         2
% 2.85/0.97  --comb_inst_mult                        10
% 2.85/0.97  
% 2.85/0.97  ------ Debug Options
% 2.85/0.97  
% 2.85/0.97  --dbg_backtrace                         false
% 2.85/0.97  --dbg_dump_prop_clauses                 false
% 2.85/0.97  --dbg_dump_prop_clauses_file            -
% 2.85/0.97  --dbg_out_stat                          false
% 2.85/0.97  ------ Parsing...
% 2.85/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.85/0.97  
% 2.85/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 2.85/0.97  
% 2.85/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.85/0.97  
% 2.85/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.85/0.97  ------ Proving...
% 2.85/0.97  ------ Problem Properties 
% 2.85/0.97  
% 2.85/0.97  
% 2.85/0.97  clauses                                 27
% 2.85/0.97  conjectures                             2
% 2.85/0.97  EPR                                     1
% 2.85/0.97  Horn                                    24
% 2.85/0.97  unary                                   14
% 2.85/0.97  binary                                  9
% 2.85/0.97  lits                                    45
% 2.85/0.97  lits eq                                 37
% 2.85/0.97  fd_pure                                 0
% 2.85/0.97  fd_pseudo                               0
% 2.85/0.97  fd_cond                                 0
% 2.85/0.97  fd_pseudo_cond                          1
% 2.85/0.97  AC symbols                              0
% 2.85/0.97  
% 2.85/0.97  ------ Schedule dynamic 5 is on 
% 2.85/0.97  
% 2.85/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.85/0.97  
% 2.85/0.97  
% 2.85/0.97  ------ 
% 2.85/0.97  Current options:
% 2.85/0.97  ------ 
% 2.85/0.97  
% 2.85/0.97  ------ Input Options
% 2.85/0.97  
% 2.85/0.97  --out_options                           all
% 2.85/0.97  --tptp_safe_out                         true
% 2.85/0.97  --problem_path                          ""
% 2.85/0.97  --include_path                          ""
% 2.85/0.97  --clausifier                            res/vclausify_rel
% 2.85/0.97  --clausifier_options                    --mode clausify
% 2.85/0.97  --stdin                                 false
% 2.85/0.97  --stats_out                             all
% 2.85/0.97  
% 2.85/0.97  ------ General Options
% 2.85/0.97  
% 2.85/0.97  --fof                                   false
% 2.85/0.97  --time_out_real                         305.
% 2.85/0.97  --time_out_virtual                      -1.
% 2.85/0.97  --symbol_type_check                     false
% 2.85/0.97  --clausify_out                          false
% 2.85/0.97  --sig_cnt_out                           false
% 2.85/0.97  --trig_cnt_out                          false
% 2.85/0.97  --trig_cnt_out_tolerance                1.
% 2.85/0.97  --trig_cnt_out_sk_spl                   false
% 2.85/0.97  --abstr_cl_out                          false
% 2.85/0.97  
% 2.85/0.97  ------ Global Options
% 2.85/0.97  
% 2.85/0.97  --schedule                              default
% 2.85/0.97  --add_important_lit                     false
% 2.85/0.97  --prop_solver_per_cl                    1000
% 2.85/0.97  --min_unsat_core                        false
% 2.85/0.97  --soft_assumptions                      false
% 2.85/0.97  --soft_lemma_size                       3
% 2.85/0.97  --prop_impl_unit_size                   0
% 2.85/0.97  --prop_impl_unit                        []
% 2.85/0.97  --share_sel_clauses                     true
% 2.85/0.97  --reset_solvers                         false
% 2.85/0.97  --bc_imp_inh                            [conj_cone]
% 2.85/0.97  --conj_cone_tolerance                   3.
% 2.85/0.97  --extra_neg_conj                        none
% 2.85/0.97  --large_theory_mode                     true
% 2.85/0.97  --prolific_symb_bound                   200
% 2.85/0.97  --lt_threshold                          2000
% 2.85/0.97  --clause_weak_htbl                      true
% 2.85/0.97  --gc_record_bc_elim                     false
% 2.85/0.97  
% 2.85/0.97  ------ Preprocessing Options
% 2.85/0.97  
% 2.85/0.97  --preprocessing_flag                    true
% 2.85/0.97  --time_out_prep_mult                    0.1
% 2.85/0.97  --splitting_mode                        input
% 2.85/0.97  --splitting_grd                         true
% 2.85/0.97  --splitting_cvd                         false
% 2.85/0.97  --splitting_cvd_svl                     false
% 2.85/0.97  --splitting_nvd                         32
% 2.85/0.97  --sub_typing                            true
% 2.85/0.97  --prep_gs_sim                           true
% 2.85/0.97  --prep_unflatten                        true
% 2.85/0.97  --prep_res_sim                          true
% 2.85/0.97  --prep_upred                            true
% 2.85/0.97  --prep_sem_filter                       exhaustive
% 2.85/0.97  --prep_sem_filter_out                   false
% 2.85/0.97  --pred_elim                             true
% 2.85/0.97  --res_sim_input                         true
% 2.85/0.97  --eq_ax_congr_red                       true
% 2.85/0.97  --pure_diseq_elim                       true
% 2.85/0.97  --brand_transform                       false
% 2.85/0.97  --non_eq_to_eq                          false
% 2.85/0.97  --prep_def_merge                        true
% 2.85/0.97  --prep_def_merge_prop_impl              false
% 2.85/0.97  --prep_def_merge_mbd                    true
% 2.85/0.97  --prep_def_merge_tr_red                 false
% 2.85/0.97  --prep_def_merge_tr_cl                  false
% 2.85/0.97  --smt_preprocessing                     true
% 2.85/0.97  --smt_ac_axioms                         fast
% 2.85/0.97  --preprocessed_out                      false
% 2.85/0.97  --preprocessed_stats                    false
% 2.85/0.97  
% 2.85/0.97  ------ Abstraction refinement Options
% 2.85/0.97  
% 2.85/0.97  --abstr_ref                             []
% 2.85/0.97  --abstr_ref_prep                        false
% 2.85/0.97  --abstr_ref_until_sat                   false
% 2.85/0.97  --abstr_ref_sig_restrict                funpre
% 2.85/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.85/0.97  --abstr_ref_under                       []
% 2.85/0.97  
% 2.85/0.97  ------ SAT Options
% 2.85/0.97  
% 2.85/0.97  --sat_mode                              false
% 2.85/0.97  --sat_fm_restart_options                ""
% 2.85/0.97  --sat_gr_def                            false
% 2.85/0.97  --sat_epr_types                         true
% 2.85/0.97  --sat_non_cyclic_types                  false
% 2.85/0.97  --sat_finite_models                     false
% 2.85/0.97  --sat_fm_lemmas                         false
% 2.85/0.97  --sat_fm_prep                           false
% 2.85/0.97  --sat_fm_uc_incr                        true
% 2.85/0.97  --sat_out_model                         small
% 2.85/0.97  --sat_out_clauses                       false
% 2.85/0.97  
% 2.85/0.97  ------ QBF Options
% 2.85/0.97  
% 2.85/0.97  --qbf_mode                              false
% 2.85/0.97  --qbf_elim_univ                         false
% 2.85/0.97  --qbf_dom_inst                          none
% 2.85/0.97  --qbf_dom_pre_inst                      false
% 2.85/0.97  --qbf_sk_in                             false
% 2.85/0.97  --qbf_pred_elim                         true
% 2.85/0.97  --qbf_split                             512
% 2.85/0.97  
% 2.85/0.97  ------ BMC1 Options
% 2.85/0.97  
% 2.85/0.97  --bmc1_incremental                      false
% 2.85/0.97  --bmc1_axioms                           reachable_all
% 2.85/0.97  --bmc1_min_bound                        0
% 2.85/0.97  --bmc1_max_bound                        -1
% 2.85/0.97  --bmc1_max_bound_default                -1
% 2.85/0.97  --bmc1_symbol_reachability              true
% 2.85/0.97  --bmc1_property_lemmas                  false
% 2.85/0.97  --bmc1_k_induction                      false
% 2.85/0.97  --bmc1_non_equiv_states                 false
% 2.85/0.97  --bmc1_deadlock                         false
% 2.85/0.97  --bmc1_ucm                              false
% 2.85/0.97  --bmc1_add_unsat_core                   none
% 2.85/0.97  --bmc1_unsat_core_children              false
% 2.85/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.85/0.97  --bmc1_out_stat                         full
% 2.85/0.97  --bmc1_ground_init                      false
% 2.85/0.97  --bmc1_pre_inst_next_state              false
% 2.85/0.97  --bmc1_pre_inst_state                   false
% 2.85/0.97  --bmc1_pre_inst_reach_state             false
% 2.85/0.97  --bmc1_out_unsat_core                   false
% 2.85/0.97  --bmc1_aig_witness_out                  false
% 2.85/0.97  --bmc1_verbose                          false
% 2.85/0.97  --bmc1_dump_clauses_tptp                false
% 2.85/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.85/0.97  --bmc1_dump_file                        -
% 2.85/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.85/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.85/0.97  --bmc1_ucm_extend_mode                  1
% 2.85/0.97  --bmc1_ucm_init_mode                    2
% 2.85/0.97  --bmc1_ucm_cone_mode                    none
% 2.85/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.85/0.97  --bmc1_ucm_relax_model                  4
% 2.85/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.85/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.85/0.97  --bmc1_ucm_layered_model                none
% 2.85/0.97  --bmc1_ucm_max_lemma_size               10
% 2.85/0.97  
% 2.85/0.97  ------ AIG Options
% 2.85/0.97  
% 2.85/0.97  --aig_mode                              false
% 2.85/0.97  
% 2.85/0.97  ------ Instantiation Options
% 2.85/0.97  
% 2.85/0.97  --instantiation_flag                    true
% 2.85/0.97  --inst_sos_flag                         false
% 2.85/0.97  --inst_sos_phase                        true
% 2.85/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.85/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.85/0.97  --inst_lit_sel_side                     none
% 2.85/0.97  --inst_solver_per_active                1400
% 2.85/0.97  --inst_solver_calls_frac                1.
% 2.85/0.97  --inst_passive_queue_type               priority_queues
% 2.85/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.85/0.97  --inst_passive_queues_freq              [25;2]
% 2.85/0.97  --inst_dismatching                      true
% 2.85/0.97  --inst_eager_unprocessed_to_passive     true
% 2.85/0.97  --inst_prop_sim_given                   true
% 2.85/0.97  --inst_prop_sim_new                     false
% 2.85/0.97  --inst_subs_new                         false
% 2.85/0.97  --inst_eq_res_simp                      false
% 2.85/0.97  --inst_subs_given                       false
% 2.85/0.97  --inst_orphan_elimination               true
% 2.85/0.97  --inst_learning_loop_flag               true
% 2.85/0.97  --inst_learning_start                   3000
% 2.85/0.97  --inst_learning_factor                  2
% 2.85/0.97  --inst_start_prop_sim_after_learn       3
% 2.85/0.97  --inst_sel_renew                        solver
% 2.85/0.97  --inst_lit_activity_flag                true
% 2.85/0.97  --inst_restr_to_given                   false
% 2.85/0.97  --inst_activity_threshold               500
% 2.85/0.97  --inst_out_proof                        true
% 2.85/0.97  
% 2.85/0.97  ------ Resolution Options
% 2.85/0.97  
% 2.85/0.97  --resolution_flag                       false
% 2.85/0.97  --res_lit_sel                           adaptive
% 2.85/0.97  --res_lit_sel_side                      none
% 2.85/0.98  --res_ordering                          kbo
% 2.85/0.98  --res_to_prop_solver                    active
% 2.85/0.98  --res_prop_simpl_new                    false
% 2.85/0.98  --res_prop_simpl_given                  true
% 2.85/0.98  --res_passive_queue_type                priority_queues
% 2.85/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.85/0.98  --res_passive_queues_freq               [15;5]
% 2.85/0.98  --res_forward_subs                      full
% 2.85/0.98  --res_backward_subs                     full
% 2.85/0.98  --res_forward_subs_resolution           true
% 2.85/0.98  --res_backward_subs_resolution          true
% 2.85/0.98  --res_orphan_elimination                true
% 2.85/0.98  --res_time_limit                        2.
% 2.85/0.98  --res_out_proof                         true
% 2.85/0.98  
% 2.85/0.98  ------ Superposition Options
% 2.85/0.98  
% 2.85/0.98  --superposition_flag                    true
% 2.85/0.98  --sup_passive_queue_type                priority_queues
% 2.85/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.85/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.85/0.98  --demod_completeness_check              fast
% 2.85/0.98  --demod_use_ground                      true
% 2.85/0.98  --sup_to_prop_solver                    passive
% 2.85/0.98  --sup_prop_simpl_new                    true
% 2.85/0.98  --sup_prop_simpl_given                  true
% 2.85/0.98  --sup_fun_splitting                     false
% 2.85/0.98  --sup_smt_interval                      50000
% 2.85/0.98  
% 2.85/0.98  ------ Superposition Simplification Setup
% 2.85/0.98  
% 2.85/0.98  --sup_indices_passive                   []
% 2.85/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.85/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.85/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.85/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.85/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.85/0.98  --sup_full_bw                           [BwDemod]
% 2.85/0.98  --sup_immed_triv                        [TrivRules]
% 2.85/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.85/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.85/0.98  --sup_immed_bw_main                     []
% 2.85/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.85/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.85/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.85/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.85/0.98  
% 2.85/0.98  ------ Combination Options
% 2.85/0.98  
% 2.85/0.98  --comb_res_mult                         3
% 2.85/0.98  --comb_sup_mult                         2
% 2.85/0.98  --comb_inst_mult                        10
% 2.85/0.98  
% 2.85/0.98  ------ Debug Options
% 2.85/0.98  
% 2.85/0.98  --dbg_backtrace                         false
% 2.85/0.98  --dbg_dump_prop_clauses                 false
% 2.85/0.98  --dbg_dump_prop_clauses_file            -
% 2.85/0.98  --dbg_out_stat                          false
% 2.85/0.98  
% 2.85/0.98  
% 2.85/0.98  
% 2.85/0.98  
% 2.85/0.98  ------ Proving...
% 2.85/0.98  
% 2.85/0.98  
% 2.85/0.98  % SZS status Theorem for theBenchmark.p
% 2.85/0.98  
% 2.85/0.98   Resolution empty clause
% 2.85/0.98  
% 2.85/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.85/0.98  
% 2.85/0.98  fof(f20,axiom,(
% 2.85/0.98    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 2.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.98  
% 2.85/0.98  fof(f75,plain,(
% 2.85/0.98    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 2.85/0.98    inference(cnf_transformation,[],[f20])).
% 2.85/0.98  
% 2.85/0.98  fof(f14,axiom,(
% 2.85/0.98    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 2.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.98  
% 2.85/0.98  fof(f68,plain,(
% 2.85/0.98    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.85/0.98    inference(cnf_transformation,[],[f14])).
% 2.85/0.98  
% 2.85/0.98  fof(f15,axiom,(
% 2.85/0.98    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 2.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.98  
% 2.85/0.98  fof(f34,plain,(
% 2.85/0.98    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.85/0.98    inference(ennf_transformation,[],[f15])).
% 2.85/0.98  
% 2.85/0.98  fof(f69,plain,(
% 2.85/0.98    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 2.85/0.98    inference(cnf_transformation,[],[f34])).
% 2.85/0.98  
% 2.85/0.98  fof(f6,axiom,(
% 2.85/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.98  
% 2.85/0.98  fof(f59,plain,(
% 2.85/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.85/0.98    inference(cnf_transformation,[],[f6])).
% 2.85/0.98  
% 2.85/0.98  fof(f104,plain,(
% 2.85/0.98    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 2.85/0.98    inference(definition_unfolding,[],[f69,f59])).
% 2.85/0.98  
% 2.85/0.98  fof(f19,axiom,(
% 2.85/0.98    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.98  
% 2.85/0.98  fof(f74,plain,(
% 2.85/0.98    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 2.85/0.98    inference(cnf_transformation,[],[f19])).
% 2.85/0.98  
% 2.85/0.98  fof(f3,axiom,(
% 2.85/0.98    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.98  
% 2.85/0.98  fof(f56,plain,(
% 2.85/0.98    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.85/0.98    inference(cnf_transformation,[],[f3])).
% 2.85/0.98  
% 2.85/0.98  fof(f98,plain,(
% 2.85/0.98    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 2.85/0.98    inference(definition_unfolding,[],[f56,f59])).
% 2.85/0.98  
% 2.85/0.98  fof(f5,axiom,(
% 2.85/0.98    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 2.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.98  
% 2.85/0.98  fof(f32,plain,(
% 2.85/0.98    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 2.85/0.98    inference(ennf_transformation,[],[f5])).
% 2.85/0.98  
% 2.85/0.98  fof(f58,plain,(
% 2.85/0.98    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 2.85/0.98    inference(cnf_transformation,[],[f32])).
% 2.85/0.98  
% 2.85/0.98  fof(f2,axiom,(
% 2.85/0.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.98  
% 2.85/0.98  fof(f55,plain,(
% 2.85/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.85/0.98    inference(cnf_transformation,[],[f2])).
% 2.85/0.98  
% 2.85/0.98  fof(f96,plain,(
% 2.85/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.85/0.98    inference(definition_unfolding,[],[f55,f59])).
% 2.85/0.98  
% 2.85/0.98  fof(f7,axiom,(
% 2.85/0.98    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.98  
% 2.85/0.98  fof(f60,plain,(
% 2.85/0.98    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.85/0.98    inference(cnf_transformation,[],[f7])).
% 2.85/0.98  
% 2.85/0.98  fof(f16,axiom,(
% 2.85/0.98    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 2.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.98  
% 2.85/0.98  fof(f35,plain,(
% 2.85/0.98    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 2.85/0.98    inference(ennf_transformation,[],[f16])).
% 2.85/0.98  
% 2.85/0.98  fof(f70,plain,(
% 2.85/0.98    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.85/0.98    inference(cnf_transformation,[],[f35])).
% 2.85/0.98  
% 2.85/0.98  fof(f73,plain,(
% 2.85/0.98    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.85/0.98    inference(cnf_transformation,[],[f19])).
% 2.85/0.98  
% 2.85/0.98  fof(f11,axiom,(
% 2.85/0.98    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 2.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.98  
% 2.85/0.98  fof(f33,plain,(
% 2.85/0.98    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 2.85/0.98    inference(ennf_transformation,[],[f11])).
% 2.85/0.98  
% 2.85/0.98  fof(f64,plain,(
% 2.85/0.98    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 2.85/0.98    inference(cnf_transformation,[],[f33])).
% 2.85/0.98  
% 2.85/0.98  fof(f8,axiom,(
% 2.85/0.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.98  
% 2.85/0.98  fof(f61,plain,(
% 2.85/0.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.85/0.98    inference(cnf_transformation,[],[f8])).
% 2.85/0.98  
% 2.85/0.98  fof(f9,axiom,(
% 2.85/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.98  
% 2.85/0.98  fof(f62,plain,(
% 2.85/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.85/0.98    inference(cnf_transformation,[],[f9])).
% 2.85/0.98  
% 2.85/0.98  fof(f10,axiom,(
% 2.85/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.98  
% 2.85/0.98  fof(f63,plain,(
% 2.85/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.85/0.98    inference(cnf_transformation,[],[f10])).
% 2.85/0.98  
% 2.85/0.98  fof(f94,plain,(
% 2.85/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.85/0.98    inference(definition_unfolding,[],[f62,f63])).
% 2.85/0.98  
% 2.85/0.98  fof(f95,plain,(
% 2.85/0.98    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.85/0.98    inference(definition_unfolding,[],[f61,f94])).
% 2.85/0.98  
% 2.85/0.98  fof(f100,plain,(
% 2.85/0.98    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 2.85/0.98    inference(definition_unfolding,[],[f64,f95])).
% 2.85/0.98  
% 2.85/0.98  fof(f17,axiom,(
% 2.85/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 2.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.98  
% 2.85/0.98  fof(f36,plain,(
% 2.85/0.98    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.85/0.98    inference(ennf_transformation,[],[f17])).
% 2.85/0.98  
% 2.85/0.98  fof(f71,plain,(
% 2.85/0.98    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.85/0.98    inference(cnf_transformation,[],[f36])).
% 2.85/0.98  
% 2.85/0.98  fof(f21,axiom,(
% 2.85/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k1_tarski(X0)))))),
% 2.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.98  
% 2.85/0.98  fof(f39,plain,(
% 2.85/0.98    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.85/0.98    inference(ennf_transformation,[],[f21])).
% 2.85/0.98  
% 2.85/0.98  fof(f40,plain,(
% 2.85/0.98    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.85/0.98    inference(flattening,[],[f39])).
% 2.85/0.98  
% 2.85/0.98  fof(f76,plain,(
% 2.85/0.98    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.85/0.98    inference(cnf_transformation,[],[f40])).
% 2.85/0.98  
% 2.85/0.98  fof(f105,plain,(
% 2.85/0.98    ( ! [X0,X1] : (k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k2_enumset1(X0,X0,X0,X0))) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.85/0.98    inference(definition_unfolding,[],[f76,f95,f95])).
% 2.85/0.98  
% 2.85/0.98  fof(f28,conjecture,(
% 2.85/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 2.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.98  
% 2.85/0.98  fof(f29,negated_conjecture,(
% 2.85/0.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 2.85/0.98    inference(negated_conjecture,[],[f28])).
% 2.85/0.98  
% 2.85/0.98  fof(f48,plain,(
% 2.85/0.98    ? [X0,X1,X2] : ((k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 2.85/0.98    inference(ennf_transformation,[],[f29])).
% 2.85/0.98  
% 2.85/0.98  fof(f49,plain,(
% 2.85/0.98    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 2.85/0.98    inference(flattening,[],[f48])).
% 2.85/0.98  
% 2.85/0.98  fof(f52,plain,(
% 2.85/0.98    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_tarski(k1_funct_1(sK2,sK0)) != k2_relset_1(k1_tarski(sK0),sK1,sK2) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2))),
% 2.85/0.98    introduced(choice_axiom,[])).
% 2.85/0.98  
% 2.85/0.98  fof(f53,plain,(
% 2.85/0.98    k1_tarski(k1_funct_1(sK2,sK0)) != k2_relset_1(k1_tarski(sK0),sK1,sK2) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2)),
% 2.85/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f49,f52])).
% 2.85/0.98  
% 2.85/0.98  fof(f89,plain,(
% 2.85/0.98    v1_funct_1(sK2)),
% 2.85/0.98    inference(cnf_transformation,[],[f53])).
% 2.85/0.98  
% 2.85/0.98  fof(f22,axiom,(
% 2.85/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.98  
% 2.85/0.98  fof(f41,plain,(
% 2.85/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.85/0.98    inference(ennf_transformation,[],[f22])).
% 2.85/0.98  
% 2.85/0.98  fof(f77,plain,(
% 2.85/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.85/0.98    inference(cnf_transformation,[],[f41])).
% 2.85/0.98  
% 2.85/0.98  fof(f91,plain,(
% 2.85/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 2.85/0.98    inference(cnf_transformation,[],[f53])).
% 2.85/0.98  
% 2.85/0.98  fof(f107,plain,(
% 2.85/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 2.85/0.98    inference(definition_unfolding,[],[f91,f95])).
% 2.85/0.98  
% 2.85/0.98  fof(f24,axiom,(
% 2.85/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.98  
% 2.85/0.98  fof(f43,plain,(
% 2.85/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.85/0.98    inference(ennf_transformation,[],[f24])).
% 2.85/0.98  
% 2.85/0.98  fof(f79,plain,(
% 2.85/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.85/0.98    inference(cnf_transformation,[],[f43])).
% 2.85/0.98  
% 2.85/0.98  fof(f93,plain,(
% 2.85/0.98    k1_tarski(k1_funct_1(sK2,sK0)) != k2_relset_1(k1_tarski(sK0),sK1,sK2)),
% 2.85/0.98    inference(cnf_transformation,[],[f53])).
% 2.85/0.98  
% 2.85/0.98  fof(f106,plain,(
% 2.85/0.98    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)),
% 2.85/0.98    inference(definition_unfolding,[],[f93,f95,f95])).
% 2.85/0.98  
% 2.85/0.98  fof(f26,axiom,(
% 2.85/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 2.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.98  
% 2.85/0.98  fof(f45,plain,(
% 2.85/0.98    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.85/0.98    inference(ennf_transformation,[],[f26])).
% 2.85/0.98  
% 2.85/0.98  fof(f82,plain,(
% 2.85/0.98    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.85/0.98    inference(cnf_transformation,[],[f45])).
% 2.85/0.98  
% 2.85/0.98  fof(f90,plain,(
% 2.85/0.98    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 2.85/0.98    inference(cnf_transformation,[],[f53])).
% 2.85/0.98  
% 2.85/0.98  fof(f108,plain,(
% 2.85/0.98    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 2.85/0.98    inference(definition_unfolding,[],[f90,f95])).
% 2.85/0.98  
% 2.85/0.98  fof(f27,axiom,(
% 2.85/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.98  
% 2.85/0.98  fof(f46,plain,(
% 2.85/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.85/0.98    inference(ennf_transformation,[],[f27])).
% 2.85/0.98  
% 2.85/0.98  fof(f47,plain,(
% 2.85/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.85/0.98    inference(flattening,[],[f46])).
% 2.85/0.98  
% 2.85/0.98  fof(f51,plain,(
% 2.85/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.85/0.98    inference(nnf_transformation,[],[f47])).
% 2.85/0.98  
% 2.85/0.98  fof(f83,plain,(
% 2.85/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.85/0.98    inference(cnf_transformation,[],[f51])).
% 2.85/0.98  
% 2.85/0.98  fof(f92,plain,(
% 2.85/0.98    k1_xboole_0 != sK1),
% 2.85/0.98    inference(cnf_transformation,[],[f53])).
% 2.85/0.98  
% 2.85/0.98  fof(f25,axiom,(
% 2.85/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 2.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.98  
% 2.85/0.98  fof(f44,plain,(
% 2.85/0.98    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.85/0.98    inference(ennf_transformation,[],[f25])).
% 2.85/0.98  
% 2.85/0.98  fof(f80,plain,(
% 2.85/0.98    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.85/0.98    inference(cnf_transformation,[],[f44])).
% 2.85/0.98  
% 2.85/0.98  fof(f23,axiom,(
% 2.85/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.98  
% 2.85/0.98  fof(f31,plain,(
% 2.85/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.85/0.98    inference(pure_predicate_removal,[],[f23])).
% 2.85/0.98  
% 2.85/0.98  fof(f42,plain,(
% 2.85/0.98    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.85/0.98    inference(ennf_transformation,[],[f31])).
% 2.85/0.98  
% 2.85/0.98  fof(f78,plain,(
% 2.85/0.98    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.85/0.98    inference(cnf_transformation,[],[f42])).
% 2.85/0.98  
% 2.85/0.98  fof(f18,axiom,(
% 2.85/0.98    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.98  
% 2.85/0.98  fof(f37,plain,(
% 2.85/0.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.85/0.98    inference(ennf_transformation,[],[f18])).
% 2.85/0.98  
% 2.85/0.98  fof(f38,plain,(
% 2.85/0.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.85/0.98    inference(flattening,[],[f37])).
% 2.85/0.98  
% 2.85/0.98  fof(f72,plain,(
% 2.85/0.98    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.85/0.98    inference(cnf_transformation,[],[f38])).
% 2.85/0.98  
% 2.85/0.98  fof(f1,axiom,(
% 2.85/0.98    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.98  
% 2.85/0.98  fof(f30,plain,(
% 2.85/0.98    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.85/0.98    inference(rectify,[],[f1])).
% 2.85/0.98  
% 2.85/0.98  fof(f54,plain,(
% 2.85/0.98    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.85/0.98    inference(cnf_transformation,[],[f30])).
% 2.85/0.98  
% 2.85/0.98  fof(f97,plain,(
% 2.85/0.98    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 2.85/0.98    inference(definition_unfolding,[],[f54,f59])).
% 2.85/0.98  
% 2.85/0.98  fof(f4,axiom,(
% 2.85/0.98    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 2.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.98  
% 2.85/0.98  fof(f57,plain,(
% 2.85/0.98    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 2.85/0.98    inference(cnf_transformation,[],[f4])).
% 2.85/0.98  
% 2.85/0.98  fof(f99,plain,(
% 2.85/0.98    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0) )),
% 2.85/0.98    inference(definition_unfolding,[],[f57,f59])).
% 2.85/0.98  
% 2.85/0.98  fof(f12,axiom,(
% 2.85/0.98    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 2.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.98  
% 2.85/0.98  fof(f50,plain,(
% 2.85/0.98    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 2.85/0.98    inference(nnf_transformation,[],[f12])).
% 2.85/0.98  
% 2.85/0.98  fof(f65,plain,(
% 2.85/0.98    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 2.85/0.98    inference(cnf_transformation,[],[f50])).
% 2.85/0.98  
% 2.85/0.98  fof(f102,plain,(
% 2.85/0.98    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) != k2_enumset1(X0,X0,X0,X0)) )),
% 2.85/0.98    inference(definition_unfolding,[],[f65,f95,f95,f95])).
% 2.85/0.98  
% 2.85/0.98  fof(f109,plain,(
% 2.85/0.98    ( ! [X1] : (k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)) != k2_enumset1(X1,X1,X1,X1)) )),
% 2.85/0.98    inference(equality_resolution,[],[f102])).
% 2.85/0.98  
% 2.85/0.98  cnf(c_17,plain,
% 2.85/0.98      ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.85/0.98      inference(cnf_transformation,[],[f75]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_10,plain,
% 2.85/0.98      ( v1_relat_1(k6_relat_1(X0)) ),
% 2.85/0.98      inference(cnf_transformation,[],[f68]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1200,plain,
% 2.85/0.98      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 2.85/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_2242,plain,
% 2.85/0.98      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 2.85/0.98      inference(superposition,[status(thm)],[c_17,c_1200]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_11,plain,
% 2.85/0.98      ( ~ v1_relat_1(X0)
% 2.85/0.98      | k10_relat_1(X0,k4_xboole_0(k2_relat_1(X0),k4_xboole_0(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1) ),
% 2.85/0.98      inference(cnf_transformation,[],[f104]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1199,plain,
% 2.85/0.98      ( k10_relat_1(X0,k4_xboole_0(k2_relat_1(X0),k4_xboole_0(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1)
% 2.85/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.85/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_3566,plain,
% 2.85/0.98      ( k10_relat_1(k1_xboole_0,k4_xboole_0(k2_relat_1(k1_xboole_0),k4_xboole_0(k2_relat_1(k1_xboole_0),X0))) = k10_relat_1(k1_xboole_0,X0) ),
% 2.85/0.98      inference(superposition,[status(thm)],[c_2242,c_1199]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_15,plain,
% 2.85/0.98      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.85/0.98      inference(cnf_transformation,[],[f74]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_2,plain,
% 2.85/0.98      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 2.85/0.98      inference(cnf_transformation,[],[f98]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_4,plain,
% 2.85/0.98      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 2.85/0.98      inference(cnf_transformation,[],[f58]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_310,plain,
% 2.85/0.98      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2
% 2.85/0.98      | k1_xboole_0 != X0
% 2.85/0.98      | k1_xboole_0 = X2 ),
% 2.85/0.98      inference(resolution_lifted,[status(thm)],[c_2,c_4]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_311,plain,
% 2.85/0.98      ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
% 2.85/0.98      inference(unflattening,[status(thm)],[c_310]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1371,plain,
% 2.85/0.98      ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.85/0.98      inference(superposition,[status(thm)],[c_311,c_311]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_0,plain,
% 2.85/0.98      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 2.85/0.98      inference(cnf_transformation,[],[f96]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1688,plain,
% 2.85/0.98      ( k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 2.85/0.98      inference(superposition,[status(thm)],[c_311,c_0]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_5,plain,
% 2.85/0.98      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.85/0.98      inference(cnf_transformation,[],[f60]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1702,plain,
% 2.85/0.98      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.85/0.98      inference(demodulation,[status(thm)],[c_1688,c_5]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_12,plain,
% 2.85/0.98      ( ~ v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 2.85/0.98      inference(cnf_transformation,[],[f70]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1198,plain,
% 2.85/0.98      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 2.85/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.85/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_3476,plain,
% 2.85/0.98      ( k10_relat_1(k1_xboole_0,k2_relat_1(k1_xboole_0)) = k1_relat_1(k1_xboole_0) ),
% 2.85/0.98      inference(superposition,[status(thm)],[c_2242,c_1198]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_16,plain,
% 2.85/0.98      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.85/0.98      inference(cnf_transformation,[],[f73]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_3478,plain,
% 2.85/0.98      ( k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.85/0.98      inference(light_normalisation,[status(thm)],[c_3476,c_15,c_16]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_3568,plain,
% 2.85/0.98      ( k10_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.85/0.98      inference(light_normalisation,
% 2.85/0.98                [status(thm)],
% 2.85/0.98                [c_3566,c_15,c_1371,c_1702,c_3478]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_6,plain,
% 2.85/0.98      ( r2_hidden(X0,X1) | r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ),
% 2.85/0.98      inference(cnf_transformation,[],[f100]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_13,plain,
% 2.85/0.98      ( ~ r1_xboole_0(X0,k1_relat_1(X1))
% 2.85/0.98      | ~ v1_relat_1(X1)
% 2.85/0.98      | k7_relat_1(X1,X0) = k1_xboole_0 ),
% 2.85/0.98      inference(cnf_transformation,[],[f71]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_317,plain,
% 2.85/0.98      ( r2_hidden(X0,X1)
% 2.85/0.98      | ~ v1_relat_1(X2)
% 2.85/0.98      | k2_enumset1(X0,X0,X0,X0) != X3
% 2.85/0.98      | k7_relat_1(X2,X3) = k1_xboole_0
% 2.85/0.98      | k1_relat_1(X2) != X1 ),
% 2.85/0.98      inference(resolution_lifted,[status(thm)],[c_6,c_13]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_318,plain,
% 2.85/0.98      ( r2_hidden(X0,k1_relat_1(X1))
% 2.85/0.98      | ~ v1_relat_1(X1)
% 2.85/0.98      | k7_relat_1(X1,k2_enumset1(X0,X0,X0,X0)) = k1_xboole_0 ),
% 2.85/0.98      inference(unflattening,[status(thm)],[c_317]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1197,plain,
% 2.85/0.98      ( k7_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k1_xboole_0
% 2.85/0.98      | r2_hidden(X1,k1_relat_1(X0)) = iProver_top
% 2.85/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.85/0.98      inference(predicate_to_equality,[status(thm)],[c_318]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_18,plain,
% 2.85/0.98      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.85/0.98      | ~ v1_funct_1(X1)
% 2.85/0.98      | ~ v1_relat_1(X1)
% 2.85/0.98      | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k2_enumset1(X0,X0,X0,X0))) ),
% 2.85/0.98      inference(cnf_transformation,[],[f105]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_35,negated_conjecture,
% 2.85/0.98      ( v1_funct_1(sK2) ),
% 2.85/0.98      inference(cnf_transformation,[],[f89]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_356,plain,
% 2.85/0.98      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.85/0.98      | ~ v1_relat_1(X1)
% 2.85/0.98      | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k2_enumset1(X0,X0,X0,X0)))
% 2.85/0.98      | sK2 != X1 ),
% 2.85/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_35]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_357,plain,
% 2.85/0.98      ( ~ r2_hidden(X0,k1_relat_1(sK2))
% 2.85/0.98      | ~ v1_relat_1(sK2)
% 2.85/0.98      | k2_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)) = k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0,X0,X0,X0))) ),
% 2.85/0.98      inference(unflattening,[status(thm)],[c_356]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1196,plain,
% 2.85/0.98      ( k2_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)) = k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0,X0,X0,X0)))
% 2.85/0.98      | r2_hidden(X0,k1_relat_1(sK2)) != iProver_top
% 2.85/0.98      | v1_relat_1(sK2) != iProver_top ),
% 2.85/0.98      inference(predicate_to_equality,[status(thm)],[c_357]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_358,plain,
% 2.85/0.98      ( k2_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)) = k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0,X0,X0,X0)))
% 2.85/0.98      | r2_hidden(X0,k1_relat_1(sK2)) != iProver_top
% 2.85/0.98      | v1_relat_1(sK2) != iProver_top ),
% 2.85/0.98      inference(predicate_to_equality,[status(thm)],[c_357]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1039,plain,( X0 = X0 ),theory(equality) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1307,plain,
% 2.85/0.98      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) = k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
% 2.85/0.98      inference(instantiation,[status(thm)],[c_1039]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_19,plain,
% 2.85/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.85/0.98      inference(cnf_transformation,[],[f77]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_33,negated_conjecture,
% 2.85/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
% 2.85/0.98      inference(cnf_transformation,[],[f107]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_589,plain,
% 2.85/0.98      ( v1_relat_1(X0)
% 2.85/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 2.85/0.98      | sK2 != X0 ),
% 2.85/0.98      inference(resolution_lifted,[status(thm)],[c_19,c_33]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_590,plain,
% 2.85/0.98      ( v1_relat_1(sK2)
% 2.85/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.85/0.98      inference(unflattening,[status(thm)],[c_589]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1313,plain,
% 2.85/0.98      ( v1_relat_1(sK2)
% 2.85/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
% 2.85/0.98      inference(instantiation,[status(thm)],[c_590]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1314,plain,
% 2.85/0.98      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
% 2.85/0.98      | v1_relat_1(sK2) = iProver_top ),
% 2.85/0.98      inference(predicate_to_equality,[status(thm)],[c_1313]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1989,plain,
% 2.85/0.98      ( r2_hidden(X0,k1_relat_1(sK2)) != iProver_top
% 2.85/0.98      | k2_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)) = k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0,X0,X0,X0))) ),
% 2.85/0.98      inference(global_propositional_subsumption,
% 2.85/0.98                [status(thm)],
% 2.85/0.98                [c_1196,c_358,c_1307,c_1314]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1990,plain,
% 2.85/0.98      ( k2_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)) = k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0,X0,X0,X0)))
% 2.85/0.98      | r2_hidden(X0,k1_relat_1(sK2)) != iProver_top ),
% 2.85/0.98      inference(renaming,[status(thm)],[c_1989]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_2095,plain,
% 2.85/0.98      ( k2_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)) = k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0,X0,X0,X0)))
% 2.85/0.98      | k7_relat_1(sK2,k2_enumset1(X0,X0,X0,X0)) = k1_xboole_0
% 2.85/0.98      | v1_relat_1(sK2) != iProver_top ),
% 2.85/0.98      inference(superposition,[status(thm)],[c_1197,c_1990]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_2111,plain,
% 2.85/0.98      ( ~ v1_relat_1(sK2)
% 2.85/0.98      | k2_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)) = k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0,X0,X0,X0)))
% 2.85/0.98      | k7_relat_1(sK2,k2_enumset1(X0,X0,X0,X0)) = k1_xboole_0 ),
% 2.85/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_2095]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_2451,plain,
% 2.85/0.98      ( k7_relat_1(sK2,k2_enumset1(X0,X0,X0,X0)) = k1_xboole_0
% 2.85/0.98      | k2_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)) = k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0,X0,X0,X0))) ),
% 2.85/0.98      inference(global_propositional_subsumption,
% 2.85/0.98                [status(thm)],
% 2.85/0.98                [c_2095,c_1307,c_1313,c_2111]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_2452,plain,
% 2.85/0.98      ( k2_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)) = k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0,X0,X0,X0)))
% 2.85/0.98      | k7_relat_1(sK2,k2_enumset1(X0,X0,X0,X0)) = k1_xboole_0 ),
% 2.85/0.98      inference(renaming,[status(thm)],[c_2451]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_21,plain,
% 2.85/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.85/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.85/0.98      inference(cnf_transformation,[],[f79]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_580,plain,
% 2.85/0.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.85/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.85/0.98      | sK2 != X2 ),
% 2.85/0.98      inference(resolution_lifted,[status(thm)],[c_21,c_33]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_581,plain,
% 2.85/0.98      ( k2_relset_1(X0,X1,sK2) = k2_relat_1(sK2)
% 2.85/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.85/0.98      inference(unflattening,[status(thm)],[c_580]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1322,plain,
% 2.85/0.98      ( k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2) ),
% 2.85/0.98      inference(equality_resolution,[status(thm)],[c_581]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_31,negated_conjecture,
% 2.85/0.98      ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) ),
% 2.85/0.98      inference(cnf_transformation,[],[f106]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1464,plain,
% 2.85/0.98      ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relat_1(sK2) ),
% 2.85/0.98      inference(demodulation,[status(thm)],[c_1322,c_31]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_2461,plain,
% 2.85/0.98      ( k7_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) = k1_xboole_0
% 2.85/0.98      | k2_relat_1(k7_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0))) != k2_relat_1(sK2) ),
% 2.85/0.98      inference(superposition,[status(thm)],[c_2452,c_1464]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_23,plain,
% 2.85/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.85/0.98      | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
% 2.85/0.98      inference(cnf_transformation,[],[f82]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_562,plain,
% 2.85/0.98      ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
% 2.85/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.85/0.98      | sK2 != X2 ),
% 2.85/0.98      inference(resolution_lifted,[status(thm)],[c_23,c_33]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_563,plain,
% 2.85/0.98      ( k8_relset_1(X0,X1,sK2,X1) = k1_relset_1(X0,X1,sK2)
% 2.85/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.85/0.98      inference(unflattening,[status(thm)],[c_562]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1356,plain,
% 2.85/0.98      ( k8_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2,sK1) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) ),
% 2.85/0.98      inference(equality_resolution,[status(thm)],[c_563]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_34,negated_conjecture,
% 2.85/0.98      ( v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
% 2.85/0.98      inference(cnf_transformation,[],[f108]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_30,plain,
% 2.85/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.85/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.85/0.98      | k1_relset_1(X1,X2,X0) = X1
% 2.85/0.98      | k1_xboole_0 = X2 ),
% 2.85/0.98      inference(cnf_transformation,[],[f83]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_517,plain,
% 2.85/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.85/0.98      | k1_relset_1(X1,X2,X0) = X1
% 2.85/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 2.85/0.98      | sK2 != X0
% 2.85/0.98      | k1_xboole_0 = X2 ),
% 2.85/0.98      inference(resolution_lifted,[status(thm)],[c_30,c_33]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_518,plain,
% 2.85/0.98      ( ~ v1_funct_2(sK2,X0,X1)
% 2.85/0.98      | k1_relset_1(X0,X1,sK2) = X0
% 2.85/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.85/0.98      | k1_xboole_0 = X1 ),
% 2.85/0.98      inference(unflattening,[status(thm)],[c_517]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_811,plain,
% 2.85/0.98      ( k2_enumset1(sK0,sK0,sK0,sK0) != X0
% 2.85/0.98      | k1_relset_1(X0,X1,sK2) = X0
% 2.85/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.85/0.98      | sK1 != X1
% 2.85/0.98      | sK2 != sK2
% 2.85/0.98      | k1_xboole_0 = X1 ),
% 2.85/0.98      inference(resolution_lifted,[status(thm)],[c_34,c_518]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_812,plain,
% 2.85/0.98      ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0)
% 2.85/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
% 2.85/0.98      | k1_xboole_0 = sK1 ),
% 2.85/0.98      inference(unflattening,[status(thm)],[c_811]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_32,negated_conjecture,
% 2.85/0.98      ( k1_xboole_0 != sK1 ),
% 2.85/0.98      inference(cnf_transformation,[],[f92]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_813,plain,
% 2.85/0.98      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
% 2.85/0.98      | k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0) ),
% 2.85/0.98      inference(global_propositional_subsumption,[status(thm)],[c_812,c_32]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_814,plain,
% 2.85/0.98      ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0)
% 2.85/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
% 2.85/0.98      inference(renaming,[status(thm)],[c_813]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_869,plain,
% 2.85/0.98      ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0) ),
% 2.85/0.98      inference(equality_resolution_simp,[status(thm)],[c_814]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1505,plain,
% 2.85/0.98      ( k8_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2,sK1) = k2_enumset1(sK0,sK0,sK0,sK0) ),
% 2.85/0.98      inference(light_normalisation,[status(thm)],[c_1356,c_869]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_22,plain,
% 2.85/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.85/0.98      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 2.85/0.98      inference(cnf_transformation,[],[f80]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_571,plain,
% 2.85/0.98      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 2.85/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.85/0.98      | sK2 != X2 ),
% 2.85/0.98      inference(resolution_lifted,[status(thm)],[c_22,c_33]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_572,plain,
% 2.85/0.98      ( k8_relset_1(X0,X1,sK2,X2) = k10_relat_1(sK2,X2)
% 2.85/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.85/0.98      inference(unflattening,[status(thm)],[c_571]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1343,plain,
% 2.85/0.98      ( k8_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2,X0) = k10_relat_1(sK2,X0) ),
% 2.85/0.98      inference(equality_resolution,[status(thm)],[c_572]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1506,plain,
% 2.85/0.98      ( k2_enumset1(sK0,sK0,sK0,sK0) = k10_relat_1(sK2,sK1) ),
% 2.85/0.98      inference(demodulation,[status(thm)],[c_1505,c_1343]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_20,plain,
% 2.85/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v4_relat_1(X0,X1) ),
% 2.85/0.98      inference(cnf_transformation,[],[f78]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_14,plain,
% 2.85/0.98      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 2.85/0.98      inference(cnf_transformation,[],[f72]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_336,plain,
% 2.85/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.85/0.98      | ~ v1_relat_1(X0)
% 2.85/0.98      | k7_relat_1(X0,X1) = X0 ),
% 2.85/0.98      inference(resolution,[status(thm)],[c_20,c_14]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_340,plain,
% 2.85/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.85/0.98      | k7_relat_1(X0,X1) = X0 ),
% 2.85/0.98      inference(global_propositional_subsumption,
% 2.85/0.98                [status(thm)],
% 2.85/0.98                [c_336,c_20,c_19,c_14]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_508,plain,
% 2.85/0.98      ( k7_relat_1(X0,X1) = X0
% 2.85/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 2.85/0.98      | sK2 != X0 ),
% 2.85/0.98      inference(resolution_lifted,[status(thm)],[c_340,c_33]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_509,plain,
% 2.85/0.98      ( k7_relat_1(sK2,X0) = sK2
% 2.85/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.85/0.98      inference(unflattening,[status(thm)],[c_508]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1319,plain,
% 2.85/0.98      ( k7_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) = sK2 ),
% 2.85/0.98      inference(equality_resolution,[status(thm)],[c_509]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1511,plain,
% 2.85/0.98      ( k7_relat_1(sK2,k10_relat_1(sK2,sK1)) = sK2 ),
% 2.85/0.98      inference(demodulation,[status(thm)],[c_1506,c_1319]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_2464,plain,
% 2.85/0.98      ( k2_relat_1(sK2) != k2_relat_1(sK2) | sK2 = k1_xboole_0 ),
% 2.85/0.98      inference(light_normalisation,[status(thm)],[c_2461,c_1506,c_1511]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_2465,plain,
% 2.85/0.98      ( sK2 = k1_xboole_0 ),
% 2.85/0.98      inference(equality_resolution_simp,[status(thm)],[c_2464]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_2506,plain,
% 2.85/0.98      ( k2_enumset1(sK0,sK0,sK0,sK0) = k10_relat_1(k1_xboole_0,sK1) ),
% 2.85/0.98      inference(demodulation,[status(thm)],[c_2465,c_1506]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_3575,plain,
% 2.85/0.98      ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_xboole_0 ),
% 2.85/0.98      inference(demodulation,[status(thm)],[c_3568,c_2506]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1,plain,
% 2.85/0.98      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 2.85/0.98      inference(cnf_transformation,[],[f97]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1686,plain,
% 2.85/0.98      ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
% 2.85/0.98      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_3,plain,
% 2.85/0.98      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 2.85/0.98      inference(cnf_transformation,[],[f99]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1687,plain,
% 2.85/0.98      ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 2.85/0.98      inference(superposition,[status(thm)],[c_3,c_0]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1705,plain,
% 2.85/0.98      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.85/0.98      inference(light_normalisation,[status(thm)],[c_1687,c_5]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1690,plain,
% 2.85/0.98      ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
% 2.85/0.98      inference(superposition,[status(thm)],[c_3,c_0]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1696,plain,
% 2.85/0.98      ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 2.85/0.98      inference(light_normalisation,[status(thm)],[c_1690,c_3]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1706,plain,
% 2.85/0.98      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 2.85/0.98      inference(demodulation,[status(thm)],[c_1705,c_1696]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1710,plain,
% 2.85/0.98      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 2.85/0.98      inference(light_normalisation,[status(thm)],[c_1686,c_1706]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_8,plain,
% 2.85/0.98      ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)) != k2_enumset1(X0,X0,X0,X0) ),
% 2.85/0.98      inference(cnf_transformation,[],[f109]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_3792,plain,
% 2.85/0.98      ( k2_enumset1(X0,X0,X0,X0) != k1_xboole_0 ),
% 2.85/0.98      inference(demodulation,[status(thm)],[c_1710,c_8]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_4170,plain,
% 2.85/0.98      ( $false ),
% 2.85/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_3575,c_3792]) ).
% 2.85/0.98  
% 2.85/0.98  
% 2.85/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.85/0.98  
% 2.85/0.98  ------                               Statistics
% 2.85/0.98  
% 2.85/0.98  ------ General
% 2.85/0.98  
% 2.85/0.98  abstr_ref_over_cycles:                  0
% 2.85/0.98  abstr_ref_under_cycles:                 0
% 2.85/0.98  gc_basic_clause_elim:                   0
% 2.85/0.98  forced_gc_time:                         0
% 2.85/0.98  parsing_time:                           0.009
% 2.85/0.98  unif_index_cands_time:                  0.
% 2.85/0.98  unif_index_add_time:                    0.
% 2.85/0.98  orderings_time:                         0.
% 2.85/0.98  out_proof_time:                         0.009
% 2.85/0.98  total_time:                             0.187
% 2.85/0.98  num_of_symbols:                         59
% 2.85/0.98  num_of_terms:                           4638
% 2.85/0.98  
% 2.85/0.98  ------ Preprocessing
% 2.85/0.98  
% 2.85/0.98  num_of_splits:                          0
% 2.85/0.98  num_of_split_atoms:                     0
% 2.85/0.98  num_of_reused_defs:                     0
% 2.85/0.98  num_eq_ax_congr_red:                    32
% 2.85/0.98  num_of_sem_filtered_clauses:            1
% 2.85/0.98  num_of_subtypes:                        0
% 2.85/0.98  monotx_restored_types:                  0
% 2.85/0.98  sat_num_of_epr_types:                   0
% 2.85/0.98  sat_num_of_non_cyclic_types:            0
% 2.85/0.98  sat_guarded_non_collapsed_types:        0
% 2.85/0.98  num_pure_diseq_elim:                    0
% 2.85/0.98  simp_replaced_by:                       0
% 2.85/0.98  res_preprocessed:                       158
% 2.85/0.98  prep_upred:                             0
% 2.85/0.98  prep_unflattend:                        52
% 2.85/0.98  smt_new_axioms:                         0
% 2.85/0.98  pred_elim_cands:                        2
% 2.85/0.98  pred_elim:                              6
% 2.85/0.98  pred_elim_cl:                           9
% 2.85/0.98  pred_elim_cycles:                       12
% 2.85/0.98  merged_defs:                            0
% 2.85/0.98  merged_defs_ncl:                        0
% 2.85/0.98  bin_hyper_res:                          0
% 2.85/0.98  prep_cycles:                            4
% 2.85/0.98  pred_elim_time:                         0.014
% 2.85/0.98  splitting_time:                         0.
% 2.85/0.98  sem_filter_time:                        0.
% 2.85/0.98  monotx_time:                            0.
% 2.85/0.98  subtype_inf_time:                       0.
% 2.85/0.98  
% 2.85/0.98  ------ Problem properties
% 2.85/0.98  
% 2.85/0.98  clauses:                                27
% 2.85/0.98  conjectures:                            2
% 2.85/0.98  epr:                                    1
% 2.85/0.98  horn:                                   24
% 2.85/0.98  ground:                                 8
% 2.85/0.98  unary:                                  14
% 2.85/0.98  binary:                                 9
% 2.85/0.98  lits:                                   45
% 2.85/0.98  lits_eq:                                37
% 2.85/0.98  fd_pure:                                0
% 2.85/0.98  fd_pseudo:                              0
% 2.85/0.98  fd_cond:                                0
% 2.85/0.98  fd_pseudo_cond:                         1
% 2.85/0.98  ac_symbols:                             0
% 2.85/0.98  
% 2.85/0.98  ------ Propositional Solver
% 2.85/0.98  
% 2.85/0.98  prop_solver_calls:                      28
% 2.85/0.98  prop_fast_solver_calls:                 894
% 2.85/0.98  smt_solver_calls:                       0
% 2.85/0.98  smt_fast_solver_calls:                  0
% 2.85/0.98  prop_num_of_clauses:                    1480
% 2.85/0.98  prop_preprocess_simplified:             5089
% 2.85/0.98  prop_fo_subsumed:                       9
% 2.85/0.98  prop_solver_time:                       0.
% 2.85/0.98  smt_solver_time:                        0.
% 2.85/0.98  smt_fast_solver_time:                   0.
% 2.85/0.98  prop_fast_solver_time:                  0.
% 2.85/0.98  prop_unsat_core_time:                   0.
% 2.85/0.98  
% 2.85/0.98  ------ QBF
% 2.85/0.98  
% 2.85/0.98  qbf_q_res:                              0
% 2.85/0.98  qbf_num_tautologies:                    0
% 2.85/0.98  qbf_prep_cycles:                        0
% 2.85/0.98  
% 2.85/0.98  ------ BMC1
% 2.85/0.98  
% 2.85/0.98  bmc1_current_bound:                     -1
% 2.85/0.98  bmc1_last_solved_bound:                 -1
% 2.85/0.98  bmc1_unsat_core_size:                   -1
% 2.85/0.98  bmc1_unsat_core_parents_size:           -1
% 2.85/0.98  bmc1_merge_next_fun:                    0
% 2.85/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.85/0.98  
% 2.85/0.98  ------ Instantiation
% 2.85/0.98  
% 2.85/0.98  inst_num_of_clauses:                    721
% 2.85/0.98  inst_num_in_passive:                    107
% 2.85/0.98  inst_num_in_active:                     296
% 2.85/0.98  inst_num_in_unprocessed:                321
% 2.85/0.98  inst_num_of_loops:                      390
% 2.85/0.98  inst_num_of_learning_restarts:          0
% 2.85/0.98  inst_num_moves_active_passive:          91
% 2.85/0.98  inst_lit_activity:                      0
% 2.85/0.98  inst_lit_activity_moves:                0
% 2.85/0.98  inst_num_tautologies:                   0
% 2.85/0.98  inst_num_prop_implied:                  0
% 2.85/0.98  inst_num_existing_simplified:           0
% 2.85/0.98  inst_num_eq_res_simplified:             0
% 2.85/0.98  inst_num_child_elim:                    0
% 2.85/0.98  inst_num_of_dismatching_blockings:      267
% 2.85/0.98  inst_num_of_non_proper_insts:           744
% 2.85/0.98  inst_num_of_duplicates:                 0
% 2.85/0.98  inst_inst_num_from_inst_to_res:         0
% 2.85/0.98  inst_dismatching_checking_time:         0.
% 2.85/0.98  
% 2.85/0.98  ------ Resolution
% 2.85/0.98  
% 2.85/0.98  res_num_of_clauses:                     0
% 2.85/0.98  res_num_in_passive:                     0
% 2.85/0.98  res_num_in_active:                      0
% 2.85/0.98  res_num_of_loops:                       162
% 2.85/0.98  res_forward_subset_subsumed:            101
% 2.85/0.98  res_backward_subset_subsumed:           8
% 2.85/0.98  res_forward_subsumed:                   0
% 2.85/0.98  res_backward_subsumed:                  0
% 2.85/0.98  res_forward_subsumption_resolution:     0
% 2.85/0.98  res_backward_subsumption_resolution:    0
% 2.85/0.98  res_clause_to_clause_subsumption:       146
% 2.85/0.98  res_orphan_elimination:                 0
% 2.85/0.98  res_tautology_del:                      39
% 2.85/0.98  res_num_eq_res_simplified:              1
% 2.85/0.98  res_num_sel_changes:                    0
% 2.85/0.98  res_moves_from_active_to_pass:          0
% 2.85/0.98  
% 2.85/0.98  ------ Superposition
% 2.85/0.98  
% 2.85/0.98  sup_time_total:                         0.
% 2.85/0.98  sup_time_generating:                    0.
% 2.85/0.98  sup_time_sim_full:                      0.
% 2.85/0.98  sup_time_sim_immed:                     0.
% 2.85/0.98  
% 2.85/0.98  sup_num_of_clauses:                     60
% 2.85/0.98  sup_num_in_active:                      33
% 2.85/0.98  sup_num_in_passive:                     27
% 2.85/0.98  sup_num_of_loops:                       76
% 2.85/0.98  sup_fw_superposition:                   19
% 2.85/0.98  sup_bw_superposition:                   36
% 2.85/0.98  sup_immediate_simplified:               35
% 2.85/0.98  sup_given_eliminated:                   0
% 2.85/0.98  comparisons_done:                       0
% 2.85/0.98  comparisons_avoided:                    8
% 2.85/0.98  
% 2.85/0.98  ------ Simplifications
% 2.85/0.98  
% 2.85/0.98  
% 2.85/0.98  sim_fw_subset_subsumed:                 0
% 2.85/0.98  sim_bw_subset_subsumed:                 0
% 2.85/0.98  sim_fw_subsumed:                        5
% 2.85/0.98  sim_bw_subsumed:                        2
% 2.85/0.98  sim_fw_subsumption_res:                 1
% 2.85/0.98  sim_bw_subsumption_res:                 0
% 2.85/0.98  sim_tautology_del:                      0
% 2.85/0.98  sim_eq_tautology_del:                   6
% 2.85/0.98  sim_eq_res_simp:                        2
% 2.85/0.98  sim_fw_demodulated:                     11
% 2.85/0.98  sim_bw_demodulated:                     45
% 2.85/0.98  sim_light_normalised:                   35
% 2.85/0.98  sim_joinable_taut:                      0
% 2.85/0.98  sim_joinable_simp:                      0
% 2.85/0.98  sim_ac_normalised:                      0
% 2.85/0.98  sim_smt_subsumption:                    0
% 2.85/0.98  
%------------------------------------------------------------------------------
