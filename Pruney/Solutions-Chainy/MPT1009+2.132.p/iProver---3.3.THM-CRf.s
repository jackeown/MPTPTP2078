%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:54 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 634 expanded)
%              Number of clauses        :   81 ( 156 expanded)
%              Number of leaves         :   22 ( 156 expanded)
%              Depth                    :   24
%              Number of atoms          :  438 (1563 expanded)
%              Number of equality atoms :  274 ( 786 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f35])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f94,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f19,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f31,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f32,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f31])).

fof(f40,plain,
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

fof(f41,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f32,f40])).

fof(f74,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f41])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f77,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f47,f48])).

fof(f78,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f46,f77])).

fof(f90,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f74,f78])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f52,plain,(
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
    inference(cnf_transformation,[],[f38])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_enumset1(X0,X0,X1,X2) = X3
      | k2_enumset1(X0,X0,X0,X2) = X3
      | k2_enumset1(X1,X1,X1,X2) = X3
      | k2_enumset1(X0,X0,X0,X1) = X3
      | k2_enumset1(X2,X2,X2,X2) = X3
      | k2_enumset1(X1,X1,X1,X1) = X3
      | k2_enumset1(X0,X0,X0,X0) = X3
      | k1_xboole_0 = X3
      | ~ r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) ) ),
    inference(definition_unfolding,[],[f52,f48,f77,f77,f77,f78,f78,f78,f48])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f76,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f89,plain,(
    ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f76,f78,f78])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f70,f78,f78])).

fof(f73,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f68,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_21,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_20,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_840,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2149,plain,
    ( r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_21,c_840])).

cnf(c_19,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_53,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_55,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_53])).

cnf(c_6,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_78,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_5,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_79,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_507,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1035,plain,
    ( v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2))
    | X0 != k2_zfmisc_1(X1,X2) ),
    inference(instantiation,[status(thm)],[c_507])).

cnf(c_1036,plain,
    ( X0 != k2_zfmisc_1(X1,X2)
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1035])).

cnf(c_1038,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1036])).

cnf(c_503,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1169,plain,
    ( X0 != X1
    | X0 = k2_zfmisc_1(X2,X3)
    | k2_zfmisc_1(X2,X3) != X1 ),
    inference(instantiation,[status(thm)],[c_503])).

cnf(c_1170,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1169])).

cnf(c_2226,plain,
    ( r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2149,c_55,c_78,c_79,c_1038,c_1170])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_851,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_853,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2238,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_851,c_853])).

cnf(c_2437,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2226,c_2238])).

cnf(c_18,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_26,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_326,plain,
    ( v4_relat_1(X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_30])).

cnf(c_327,plain,
    ( v4_relat_1(sK3,X0)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_326])).

cnf(c_348,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | X2 != X1
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_327])).

cnf(c_349,plain,
    ( r1_tarski(k1_relat_1(sK3),X0)
    | ~ v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_348])).

cnf(c_834,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | r1_tarski(k1_relat_1(sK3),X0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_349])).

cnf(c_350,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | r1_tarski(k1_relat_1(sK3),X0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_349])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_302,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_30])).

cnf(c_303,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_302])).

cnf(c_997,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_303])).

cnf(c_998,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(k2_zfmisc_1(X0,X1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_997])).

cnf(c_1118,plain,
    ( r1_tarski(k1_relat_1(sK3),X0) = iProver_top
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_834,c_53,c_350,c_998])).

cnf(c_1119,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | r1_tarski(k1_relat_1(sK3),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_1118])).

cnf(c_1126,plain,
    ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1119])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X2,X3))
    | k2_enumset1(X1,X1,X2,X3) = X0
    | k2_enumset1(X1,X1,X1,X3) = X0
    | k2_enumset1(X2,X2,X2,X3) = X0
    | k2_enumset1(X1,X1,X1,X2) = X0
    | k2_enumset1(X3,X3,X3,X3) = X0
    | k2_enumset1(X2,X2,X2,X2) = X0
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_842,plain,
    ( k2_enumset1(X0,X0,X1,X2) = X3
    | k2_enumset1(X0,X0,X0,X2) = X3
    | k2_enumset1(X1,X1,X1,X2) = X3
    | k2_enumset1(X0,X0,X0,X1) = X3
    | k2_enumset1(X2,X2,X2,X2) = X3
    | k2_enumset1(X1,X1,X1,X1) = X3
    | k2_enumset1(X0,X0,X0,X0) = X3
    | k1_xboole_0 = X3
    | r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2427,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1126,c_842])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_317,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_30])).

cnf(c_318,plain,
    ( k7_relset_1(X0,X1,sK3,X2) = k9_relat_1(sK3,X2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_317])).

cnf(c_2501,plain,
    ( k7_relset_1(X0,X1,sK3,X2) = k9_relat_1(sK3,X2)
    | k1_relat_1(sK3) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(superposition,[status(thm)],[c_2427,c_318])).

cnf(c_28,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_502,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1002,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) = k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_502])).

cnf(c_835,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_303])).

cnf(c_1046,plain,
    ( v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_835])).

cnf(c_1047,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | v1_relat_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1046])).

cnf(c_1003,plain,
    ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_318])).

cnf(c_1103,plain,
    ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) = k9_relat_1(sK3,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_1003])).

cnf(c_1311,plain,
    ( v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1312,plain,
    ( v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1311])).

cnf(c_1399,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_504,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1048,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != X0
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X1 ),
    inference(instantiation,[status(thm)],[c_504])).

cnf(c_1104,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | ~ r1_tarski(k9_relat_1(sK3,sK2),X0)
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X0 ),
    inference(instantiation,[status(thm)],[c_1048])).

cnf(c_1400,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1104])).

cnf(c_25,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_283,plain,
    ( ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_31])).

cnf(c_284,plain,
    ( ~ v1_relat_1(sK3)
    | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_283])).

cnf(c_836,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_284])).

cnf(c_2489,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2427,c_836])).

cnf(c_2722,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2501,c_28,c_1002,c_1046,c_1047,c_1103,c_1311,c_1312,c_1399,c_1400,c_2489])).

cnf(c_24,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_838,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2746,plain,
    ( sK3 = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2722,c_838])).

cnf(c_2749,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2746,c_1046,c_1312])).

cnf(c_995,plain,
    ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(equality_resolution,[status(thm)],[c_318])).

cnf(c_837,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1021,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_995,c_837])).

cnf(c_2758,plain,
    ( r1_tarski(k9_relat_1(k1_xboole_0,sK2),k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2749,c_1021])).

cnf(c_3386,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2437,c_2758])).

cnf(c_3666,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3386,c_851])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:22:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.27/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.03  
% 2.27/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.27/1.03  
% 2.27/1.03  ------  iProver source info
% 2.27/1.03  
% 2.27/1.03  git: date: 2020-06-30 10:37:57 +0100
% 2.27/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.27/1.03  git: non_committed_changes: false
% 2.27/1.03  git: last_make_outside_of_git: false
% 2.27/1.03  
% 2.27/1.03  ------ 
% 2.27/1.03  
% 2.27/1.03  ------ Input Options
% 2.27/1.03  
% 2.27/1.03  --out_options                           all
% 2.27/1.03  --tptp_safe_out                         true
% 2.27/1.03  --problem_path                          ""
% 2.27/1.03  --include_path                          ""
% 2.27/1.03  --clausifier                            res/vclausify_rel
% 2.27/1.03  --clausifier_options                    --mode clausify
% 2.27/1.03  --stdin                                 false
% 2.27/1.03  --stats_out                             all
% 2.27/1.03  
% 2.27/1.03  ------ General Options
% 2.27/1.03  
% 2.27/1.03  --fof                                   false
% 2.27/1.03  --time_out_real                         305.
% 2.27/1.03  --time_out_virtual                      -1.
% 2.27/1.03  --symbol_type_check                     false
% 2.27/1.03  --clausify_out                          false
% 2.27/1.03  --sig_cnt_out                           false
% 2.27/1.03  --trig_cnt_out                          false
% 2.27/1.03  --trig_cnt_out_tolerance                1.
% 2.27/1.03  --trig_cnt_out_sk_spl                   false
% 2.27/1.03  --abstr_cl_out                          false
% 2.27/1.03  
% 2.27/1.03  ------ Global Options
% 2.27/1.03  
% 2.27/1.03  --schedule                              default
% 2.27/1.03  --add_important_lit                     false
% 2.27/1.03  --prop_solver_per_cl                    1000
% 2.27/1.03  --min_unsat_core                        false
% 2.27/1.03  --soft_assumptions                      false
% 2.27/1.03  --soft_lemma_size                       3
% 2.27/1.03  --prop_impl_unit_size                   0
% 2.27/1.03  --prop_impl_unit                        []
% 2.27/1.03  --share_sel_clauses                     true
% 2.27/1.03  --reset_solvers                         false
% 2.27/1.03  --bc_imp_inh                            [conj_cone]
% 2.27/1.03  --conj_cone_tolerance                   3.
% 2.27/1.03  --extra_neg_conj                        none
% 2.27/1.03  --large_theory_mode                     true
% 2.27/1.03  --prolific_symb_bound                   200
% 2.27/1.03  --lt_threshold                          2000
% 2.27/1.03  --clause_weak_htbl                      true
% 2.27/1.03  --gc_record_bc_elim                     false
% 2.27/1.03  
% 2.27/1.03  ------ Preprocessing Options
% 2.27/1.03  
% 2.27/1.03  --preprocessing_flag                    true
% 2.27/1.03  --time_out_prep_mult                    0.1
% 2.27/1.03  --splitting_mode                        input
% 2.27/1.03  --splitting_grd                         true
% 2.27/1.03  --splitting_cvd                         false
% 2.27/1.03  --splitting_cvd_svl                     false
% 2.27/1.03  --splitting_nvd                         32
% 2.27/1.03  --sub_typing                            true
% 2.27/1.03  --prep_gs_sim                           true
% 2.27/1.03  --prep_unflatten                        true
% 2.27/1.03  --prep_res_sim                          true
% 2.27/1.03  --prep_upred                            true
% 2.27/1.03  --prep_sem_filter                       exhaustive
% 2.27/1.03  --prep_sem_filter_out                   false
% 2.27/1.03  --pred_elim                             true
% 2.27/1.03  --res_sim_input                         true
% 2.27/1.03  --eq_ax_congr_red                       true
% 2.27/1.03  --pure_diseq_elim                       true
% 2.27/1.03  --brand_transform                       false
% 2.27/1.03  --non_eq_to_eq                          false
% 2.27/1.03  --prep_def_merge                        true
% 2.27/1.03  --prep_def_merge_prop_impl              false
% 2.27/1.03  --prep_def_merge_mbd                    true
% 2.27/1.03  --prep_def_merge_tr_red                 false
% 2.27/1.03  --prep_def_merge_tr_cl                  false
% 2.27/1.03  --smt_preprocessing                     true
% 2.27/1.03  --smt_ac_axioms                         fast
% 2.27/1.03  --preprocessed_out                      false
% 2.27/1.03  --preprocessed_stats                    false
% 2.27/1.03  
% 2.27/1.03  ------ Abstraction refinement Options
% 2.27/1.03  
% 2.27/1.03  --abstr_ref                             []
% 2.27/1.03  --abstr_ref_prep                        false
% 2.27/1.03  --abstr_ref_until_sat                   false
% 2.27/1.03  --abstr_ref_sig_restrict                funpre
% 2.27/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.27/1.03  --abstr_ref_under                       []
% 2.27/1.03  
% 2.27/1.03  ------ SAT Options
% 2.27/1.03  
% 2.27/1.03  --sat_mode                              false
% 2.27/1.03  --sat_fm_restart_options                ""
% 2.27/1.03  --sat_gr_def                            false
% 2.27/1.03  --sat_epr_types                         true
% 2.27/1.03  --sat_non_cyclic_types                  false
% 2.27/1.03  --sat_finite_models                     false
% 2.27/1.03  --sat_fm_lemmas                         false
% 2.27/1.03  --sat_fm_prep                           false
% 2.27/1.03  --sat_fm_uc_incr                        true
% 2.27/1.03  --sat_out_model                         small
% 2.27/1.03  --sat_out_clauses                       false
% 2.27/1.03  
% 2.27/1.03  ------ QBF Options
% 2.27/1.03  
% 2.27/1.03  --qbf_mode                              false
% 2.27/1.03  --qbf_elim_univ                         false
% 2.27/1.03  --qbf_dom_inst                          none
% 2.27/1.03  --qbf_dom_pre_inst                      false
% 2.27/1.03  --qbf_sk_in                             false
% 2.27/1.03  --qbf_pred_elim                         true
% 2.27/1.03  --qbf_split                             512
% 2.27/1.03  
% 2.27/1.03  ------ BMC1 Options
% 2.27/1.03  
% 2.27/1.03  --bmc1_incremental                      false
% 2.27/1.03  --bmc1_axioms                           reachable_all
% 2.27/1.03  --bmc1_min_bound                        0
% 2.27/1.03  --bmc1_max_bound                        -1
% 2.27/1.03  --bmc1_max_bound_default                -1
% 2.27/1.03  --bmc1_symbol_reachability              true
% 2.27/1.03  --bmc1_property_lemmas                  false
% 2.27/1.03  --bmc1_k_induction                      false
% 2.27/1.03  --bmc1_non_equiv_states                 false
% 2.27/1.03  --bmc1_deadlock                         false
% 2.27/1.03  --bmc1_ucm                              false
% 2.27/1.03  --bmc1_add_unsat_core                   none
% 2.27/1.03  --bmc1_unsat_core_children              false
% 2.27/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.27/1.03  --bmc1_out_stat                         full
% 2.27/1.03  --bmc1_ground_init                      false
% 2.27/1.03  --bmc1_pre_inst_next_state              false
% 2.27/1.03  --bmc1_pre_inst_state                   false
% 2.27/1.03  --bmc1_pre_inst_reach_state             false
% 2.27/1.03  --bmc1_out_unsat_core                   false
% 2.27/1.03  --bmc1_aig_witness_out                  false
% 2.27/1.03  --bmc1_verbose                          false
% 2.27/1.03  --bmc1_dump_clauses_tptp                false
% 2.27/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.27/1.03  --bmc1_dump_file                        -
% 2.27/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.27/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.27/1.03  --bmc1_ucm_extend_mode                  1
% 2.27/1.03  --bmc1_ucm_init_mode                    2
% 2.27/1.03  --bmc1_ucm_cone_mode                    none
% 2.27/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.27/1.03  --bmc1_ucm_relax_model                  4
% 2.27/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.27/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.27/1.03  --bmc1_ucm_layered_model                none
% 2.27/1.03  --bmc1_ucm_max_lemma_size               10
% 2.27/1.03  
% 2.27/1.03  ------ AIG Options
% 2.27/1.03  
% 2.27/1.03  --aig_mode                              false
% 2.27/1.03  
% 2.27/1.03  ------ Instantiation Options
% 2.27/1.03  
% 2.27/1.03  --instantiation_flag                    true
% 2.27/1.03  --inst_sos_flag                         false
% 2.27/1.03  --inst_sos_phase                        true
% 2.27/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.27/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.27/1.03  --inst_lit_sel_side                     num_symb
% 2.27/1.03  --inst_solver_per_active                1400
% 2.27/1.03  --inst_solver_calls_frac                1.
% 2.27/1.03  --inst_passive_queue_type               priority_queues
% 2.27/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.27/1.03  --inst_passive_queues_freq              [25;2]
% 2.27/1.03  --inst_dismatching                      true
% 2.27/1.03  --inst_eager_unprocessed_to_passive     true
% 2.27/1.03  --inst_prop_sim_given                   true
% 2.27/1.03  --inst_prop_sim_new                     false
% 2.27/1.03  --inst_subs_new                         false
% 2.27/1.03  --inst_eq_res_simp                      false
% 2.27/1.03  --inst_subs_given                       false
% 2.27/1.03  --inst_orphan_elimination               true
% 2.27/1.03  --inst_learning_loop_flag               true
% 2.27/1.03  --inst_learning_start                   3000
% 2.27/1.03  --inst_learning_factor                  2
% 2.27/1.03  --inst_start_prop_sim_after_learn       3
% 2.27/1.03  --inst_sel_renew                        solver
% 2.27/1.03  --inst_lit_activity_flag                true
% 2.27/1.03  --inst_restr_to_given                   false
% 2.27/1.03  --inst_activity_threshold               500
% 2.27/1.03  --inst_out_proof                        true
% 2.27/1.03  
% 2.27/1.03  ------ Resolution Options
% 2.27/1.03  
% 2.27/1.03  --resolution_flag                       true
% 2.27/1.03  --res_lit_sel                           adaptive
% 2.27/1.03  --res_lit_sel_side                      none
% 2.27/1.03  --res_ordering                          kbo
% 2.27/1.03  --res_to_prop_solver                    active
% 2.27/1.03  --res_prop_simpl_new                    false
% 2.27/1.03  --res_prop_simpl_given                  true
% 2.27/1.03  --res_passive_queue_type                priority_queues
% 2.27/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.27/1.03  --res_passive_queues_freq               [15;5]
% 2.27/1.03  --res_forward_subs                      full
% 2.27/1.03  --res_backward_subs                     full
% 2.27/1.03  --res_forward_subs_resolution           true
% 2.27/1.03  --res_backward_subs_resolution          true
% 2.27/1.03  --res_orphan_elimination                true
% 2.27/1.03  --res_time_limit                        2.
% 2.27/1.03  --res_out_proof                         true
% 2.27/1.03  
% 2.27/1.03  ------ Superposition Options
% 2.27/1.03  
% 2.27/1.03  --superposition_flag                    true
% 2.27/1.03  --sup_passive_queue_type                priority_queues
% 2.27/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.27/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.27/1.03  --demod_completeness_check              fast
% 2.27/1.03  --demod_use_ground                      true
% 2.27/1.03  --sup_to_prop_solver                    passive
% 2.27/1.03  --sup_prop_simpl_new                    true
% 2.27/1.03  --sup_prop_simpl_given                  true
% 2.27/1.03  --sup_fun_splitting                     false
% 2.27/1.03  --sup_smt_interval                      50000
% 2.27/1.03  
% 2.27/1.03  ------ Superposition Simplification Setup
% 2.27/1.03  
% 2.27/1.03  --sup_indices_passive                   []
% 2.27/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.27/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/1.03  --sup_full_bw                           [BwDemod]
% 2.27/1.03  --sup_immed_triv                        [TrivRules]
% 2.27/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.27/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/1.03  --sup_immed_bw_main                     []
% 2.27/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.27/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.27/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.27/1.03  
% 2.27/1.03  ------ Combination Options
% 2.27/1.03  
% 2.27/1.03  --comb_res_mult                         3
% 2.27/1.03  --comb_sup_mult                         2
% 2.27/1.03  --comb_inst_mult                        10
% 2.27/1.03  
% 2.27/1.03  ------ Debug Options
% 2.27/1.03  
% 2.27/1.03  --dbg_backtrace                         false
% 2.27/1.03  --dbg_dump_prop_clauses                 false
% 2.27/1.03  --dbg_dump_prop_clauses_file            -
% 2.27/1.03  --dbg_out_stat                          false
% 2.27/1.03  ------ Parsing...
% 2.27/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.27/1.03  
% 2.27/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.27/1.03  
% 2.27/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.27/1.03  
% 2.27/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.27/1.03  ------ Proving...
% 2.27/1.03  ------ Problem Properties 
% 2.27/1.03  
% 2.27/1.03  
% 2.27/1.03  clauses                                 27
% 2.27/1.03  conjectures                             2
% 2.27/1.03  EPR                                     4
% 2.27/1.03  Horn                                    25
% 2.27/1.03  unary                                   17
% 2.27/1.03  binary                                  2
% 2.27/1.03  lits                                    51
% 2.27/1.03  lits eq                                 27
% 2.27/1.03  fd_pure                                 0
% 2.27/1.03  fd_pseudo                               0
% 2.27/1.03  fd_cond                                 3
% 2.27/1.03  fd_pseudo_cond                          2
% 2.27/1.03  AC symbols                              0
% 2.27/1.03  
% 2.27/1.03  ------ Schedule dynamic 5 is on 
% 2.27/1.03  
% 2.27/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.27/1.03  
% 2.27/1.03  
% 2.27/1.03  ------ 
% 2.27/1.03  Current options:
% 2.27/1.03  ------ 
% 2.27/1.03  
% 2.27/1.03  ------ Input Options
% 2.27/1.03  
% 2.27/1.03  --out_options                           all
% 2.27/1.03  --tptp_safe_out                         true
% 2.27/1.03  --problem_path                          ""
% 2.27/1.03  --include_path                          ""
% 2.27/1.03  --clausifier                            res/vclausify_rel
% 2.27/1.03  --clausifier_options                    --mode clausify
% 2.27/1.03  --stdin                                 false
% 2.27/1.03  --stats_out                             all
% 2.27/1.03  
% 2.27/1.03  ------ General Options
% 2.27/1.03  
% 2.27/1.03  --fof                                   false
% 2.27/1.03  --time_out_real                         305.
% 2.27/1.03  --time_out_virtual                      -1.
% 2.27/1.03  --symbol_type_check                     false
% 2.27/1.03  --clausify_out                          false
% 2.27/1.03  --sig_cnt_out                           false
% 2.27/1.03  --trig_cnt_out                          false
% 2.27/1.03  --trig_cnt_out_tolerance                1.
% 2.27/1.03  --trig_cnt_out_sk_spl                   false
% 2.27/1.03  --abstr_cl_out                          false
% 2.27/1.03  
% 2.27/1.03  ------ Global Options
% 2.27/1.03  
% 2.27/1.03  --schedule                              default
% 2.27/1.03  --add_important_lit                     false
% 2.27/1.03  --prop_solver_per_cl                    1000
% 2.27/1.03  --min_unsat_core                        false
% 2.27/1.03  --soft_assumptions                      false
% 2.27/1.03  --soft_lemma_size                       3
% 2.27/1.03  --prop_impl_unit_size                   0
% 2.27/1.03  --prop_impl_unit                        []
% 2.27/1.03  --share_sel_clauses                     true
% 2.27/1.03  --reset_solvers                         false
% 2.27/1.03  --bc_imp_inh                            [conj_cone]
% 2.27/1.03  --conj_cone_tolerance                   3.
% 2.27/1.03  --extra_neg_conj                        none
% 2.27/1.03  --large_theory_mode                     true
% 2.27/1.03  --prolific_symb_bound                   200
% 2.27/1.03  --lt_threshold                          2000
% 2.27/1.03  --clause_weak_htbl                      true
% 2.27/1.03  --gc_record_bc_elim                     false
% 2.27/1.03  
% 2.27/1.03  ------ Preprocessing Options
% 2.27/1.03  
% 2.27/1.03  --preprocessing_flag                    true
% 2.27/1.03  --time_out_prep_mult                    0.1
% 2.27/1.03  --splitting_mode                        input
% 2.27/1.03  --splitting_grd                         true
% 2.27/1.03  --splitting_cvd                         false
% 2.27/1.03  --splitting_cvd_svl                     false
% 2.27/1.03  --splitting_nvd                         32
% 2.27/1.03  --sub_typing                            true
% 2.27/1.03  --prep_gs_sim                           true
% 2.27/1.03  --prep_unflatten                        true
% 2.27/1.03  --prep_res_sim                          true
% 2.27/1.03  --prep_upred                            true
% 2.27/1.03  --prep_sem_filter                       exhaustive
% 2.27/1.03  --prep_sem_filter_out                   false
% 2.27/1.03  --pred_elim                             true
% 2.27/1.03  --res_sim_input                         true
% 2.27/1.03  --eq_ax_congr_red                       true
% 2.27/1.03  --pure_diseq_elim                       true
% 2.27/1.03  --brand_transform                       false
% 2.27/1.03  --non_eq_to_eq                          false
% 2.27/1.03  --prep_def_merge                        true
% 2.27/1.03  --prep_def_merge_prop_impl              false
% 2.27/1.03  --prep_def_merge_mbd                    true
% 2.27/1.03  --prep_def_merge_tr_red                 false
% 2.27/1.03  --prep_def_merge_tr_cl                  false
% 2.27/1.03  --smt_preprocessing                     true
% 2.27/1.03  --smt_ac_axioms                         fast
% 2.27/1.03  --preprocessed_out                      false
% 2.27/1.03  --preprocessed_stats                    false
% 2.27/1.03  
% 2.27/1.03  ------ Abstraction refinement Options
% 2.27/1.03  
% 2.27/1.03  --abstr_ref                             []
% 2.27/1.03  --abstr_ref_prep                        false
% 2.27/1.03  --abstr_ref_until_sat                   false
% 2.27/1.03  --abstr_ref_sig_restrict                funpre
% 2.27/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.27/1.03  --abstr_ref_under                       []
% 2.27/1.03  
% 2.27/1.03  ------ SAT Options
% 2.27/1.03  
% 2.27/1.03  --sat_mode                              false
% 2.27/1.03  --sat_fm_restart_options                ""
% 2.27/1.03  --sat_gr_def                            false
% 2.27/1.03  --sat_epr_types                         true
% 2.27/1.03  --sat_non_cyclic_types                  false
% 2.27/1.03  --sat_finite_models                     false
% 2.27/1.03  --sat_fm_lemmas                         false
% 2.27/1.03  --sat_fm_prep                           false
% 2.27/1.03  --sat_fm_uc_incr                        true
% 2.27/1.03  --sat_out_model                         small
% 2.27/1.03  --sat_out_clauses                       false
% 2.27/1.03  
% 2.27/1.03  ------ QBF Options
% 2.27/1.03  
% 2.27/1.03  --qbf_mode                              false
% 2.27/1.03  --qbf_elim_univ                         false
% 2.27/1.03  --qbf_dom_inst                          none
% 2.27/1.03  --qbf_dom_pre_inst                      false
% 2.27/1.03  --qbf_sk_in                             false
% 2.27/1.03  --qbf_pred_elim                         true
% 2.27/1.03  --qbf_split                             512
% 2.27/1.03  
% 2.27/1.03  ------ BMC1 Options
% 2.27/1.03  
% 2.27/1.03  --bmc1_incremental                      false
% 2.27/1.03  --bmc1_axioms                           reachable_all
% 2.27/1.03  --bmc1_min_bound                        0
% 2.27/1.03  --bmc1_max_bound                        -1
% 2.27/1.03  --bmc1_max_bound_default                -1
% 2.27/1.03  --bmc1_symbol_reachability              true
% 2.27/1.03  --bmc1_property_lemmas                  false
% 2.27/1.03  --bmc1_k_induction                      false
% 2.27/1.03  --bmc1_non_equiv_states                 false
% 2.27/1.03  --bmc1_deadlock                         false
% 2.27/1.03  --bmc1_ucm                              false
% 2.27/1.03  --bmc1_add_unsat_core                   none
% 2.27/1.03  --bmc1_unsat_core_children              false
% 2.27/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.27/1.03  --bmc1_out_stat                         full
% 2.27/1.03  --bmc1_ground_init                      false
% 2.27/1.03  --bmc1_pre_inst_next_state              false
% 2.27/1.03  --bmc1_pre_inst_state                   false
% 2.27/1.03  --bmc1_pre_inst_reach_state             false
% 2.27/1.03  --bmc1_out_unsat_core                   false
% 2.27/1.03  --bmc1_aig_witness_out                  false
% 2.27/1.03  --bmc1_verbose                          false
% 2.27/1.03  --bmc1_dump_clauses_tptp                false
% 2.27/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.27/1.03  --bmc1_dump_file                        -
% 2.27/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.27/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.27/1.03  --bmc1_ucm_extend_mode                  1
% 2.27/1.03  --bmc1_ucm_init_mode                    2
% 2.27/1.03  --bmc1_ucm_cone_mode                    none
% 2.27/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.27/1.03  --bmc1_ucm_relax_model                  4
% 2.27/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.27/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.27/1.03  --bmc1_ucm_layered_model                none
% 2.27/1.03  --bmc1_ucm_max_lemma_size               10
% 2.27/1.03  
% 2.27/1.03  ------ AIG Options
% 2.27/1.03  
% 2.27/1.03  --aig_mode                              false
% 2.27/1.03  
% 2.27/1.03  ------ Instantiation Options
% 2.27/1.03  
% 2.27/1.03  --instantiation_flag                    true
% 2.27/1.03  --inst_sos_flag                         false
% 2.27/1.03  --inst_sos_phase                        true
% 2.27/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.27/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.27/1.03  --inst_lit_sel_side                     none
% 2.27/1.03  --inst_solver_per_active                1400
% 2.27/1.03  --inst_solver_calls_frac                1.
% 2.27/1.03  --inst_passive_queue_type               priority_queues
% 2.27/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.27/1.03  --inst_passive_queues_freq              [25;2]
% 2.27/1.03  --inst_dismatching                      true
% 2.27/1.03  --inst_eager_unprocessed_to_passive     true
% 2.27/1.03  --inst_prop_sim_given                   true
% 2.27/1.03  --inst_prop_sim_new                     false
% 2.27/1.03  --inst_subs_new                         false
% 2.27/1.03  --inst_eq_res_simp                      false
% 2.27/1.03  --inst_subs_given                       false
% 2.27/1.03  --inst_orphan_elimination               true
% 2.27/1.03  --inst_learning_loop_flag               true
% 2.27/1.03  --inst_learning_start                   3000
% 2.27/1.03  --inst_learning_factor                  2
% 2.27/1.03  --inst_start_prop_sim_after_learn       3
% 2.27/1.03  --inst_sel_renew                        solver
% 2.27/1.03  --inst_lit_activity_flag                true
% 2.27/1.03  --inst_restr_to_given                   false
% 2.27/1.03  --inst_activity_threshold               500
% 2.27/1.03  --inst_out_proof                        true
% 2.27/1.03  
% 2.27/1.03  ------ Resolution Options
% 2.27/1.03  
% 2.27/1.03  --resolution_flag                       false
% 2.27/1.03  --res_lit_sel                           adaptive
% 2.27/1.03  --res_lit_sel_side                      none
% 2.27/1.03  --res_ordering                          kbo
% 2.27/1.03  --res_to_prop_solver                    active
% 2.27/1.03  --res_prop_simpl_new                    false
% 2.27/1.03  --res_prop_simpl_given                  true
% 2.27/1.03  --res_passive_queue_type                priority_queues
% 2.27/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.27/1.03  --res_passive_queues_freq               [15;5]
% 2.27/1.03  --res_forward_subs                      full
% 2.27/1.03  --res_backward_subs                     full
% 2.27/1.03  --res_forward_subs_resolution           true
% 2.27/1.03  --res_backward_subs_resolution          true
% 2.27/1.03  --res_orphan_elimination                true
% 2.27/1.03  --res_time_limit                        2.
% 2.27/1.03  --res_out_proof                         true
% 2.27/1.03  
% 2.27/1.03  ------ Superposition Options
% 2.27/1.03  
% 2.27/1.03  --superposition_flag                    true
% 2.27/1.03  --sup_passive_queue_type                priority_queues
% 2.27/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.27/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.27/1.03  --demod_completeness_check              fast
% 2.27/1.03  --demod_use_ground                      true
% 2.27/1.03  --sup_to_prop_solver                    passive
% 2.27/1.03  --sup_prop_simpl_new                    true
% 2.27/1.03  --sup_prop_simpl_given                  true
% 2.27/1.03  --sup_fun_splitting                     false
% 2.27/1.03  --sup_smt_interval                      50000
% 2.27/1.03  
% 2.27/1.03  ------ Superposition Simplification Setup
% 2.27/1.03  
% 2.27/1.03  --sup_indices_passive                   []
% 2.27/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.27/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/1.03  --sup_full_bw                           [BwDemod]
% 2.27/1.03  --sup_immed_triv                        [TrivRules]
% 2.27/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.27/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/1.03  --sup_immed_bw_main                     []
% 2.27/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.27/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.27/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.27/1.03  
% 2.27/1.03  ------ Combination Options
% 2.27/1.03  
% 2.27/1.03  --comb_res_mult                         3
% 2.27/1.03  --comb_sup_mult                         2
% 2.27/1.03  --comb_inst_mult                        10
% 2.27/1.03  
% 2.27/1.03  ------ Debug Options
% 2.27/1.03  
% 2.27/1.03  --dbg_backtrace                         false
% 2.27/1.03  --dbg_dump_prop_clauses                 false
% 2.27/1.03  --dbg_dump_prop_clauses_file            -
% 2.27/1.03  --dbg_out_stat                          false
% 2.27/1.03  
% 2.27/1.03  
% 2.27/1.03  
% 2.27/1.03  
% 2.27/1.03  ------ Proving...
% 2.27/1.03  
% 2.27/1.03  
% 2.27/1.03  % SZS status Theorem for theBenchmark.p
% 2.27/1.03  
% 2.27/1.03   Resolution empty clause
% 2.27/1.03  
% 2.27/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 2.27/1.03  
% 2.27/1.03  fof(f12,axiom,(
% 2.27/1.03    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.27/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/1.03  
% 2.27/1.03  fof(f67,plain,(
% 2.27/1.03    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 2.27/1.03    inference(cnf_transformation,[],[f12])).
% 2.27/1.03  
% 2.27/1.03  fof(f11,axiom,(
% 2.27/1.03    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 2.27/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/1.03  
% 2.27/1.03  fof(f24,plain,(
% 2.27/1.03    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.27/1.03    inference(ennf_transformation,[],[f11])).
% 2.27/1.03  
% 2.27/1.03  fof(f65,plain,(
% 2.27/1.03    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.27/1.03    inference(cnf_transformation,[],[f24])).
% 2.27/1.03  
% 2.27/1.03  fof(f10,axiom,(
% 2.27/1.03    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.27/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/1.03  
% 2.27/1.03  fof(f64,plain,(
% 2.27/1.03    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.27/1.03    inference(cnf_transformation,[],[f10])).
% 2.27/1.03  
% 2.27/1.03  fof(f6,axiom,(
% 2.27/1.03    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.27/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/1.03  
% 2.27/1.03  fof(f35,plain,(
% 2.27/1.03    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.27/1.03    inference(nnf_transformation,[],[f6])).
% 2.27/1.03  
% 2.27/1.03  fof(f36,plain,(
% 2.27/1.03    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.27/1.03    inference(flattening,[],[f35])).
% 2.27/1.03  
% 2.27/1.03  fof(f49,plain,(
% 2.27/1.03    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 2.27/1.03    inference(cnf_transformation,[],[f36])).
% 2.27/1.03  
% 2.27/1.03  fof(f50,plain,(
% 2.27/1.03    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.27/1.03    inference(cnf_transformation,[],[f36])).
% 2.27/1.03  
% 2.27/1.03  fof(f94,plain,(
% 2.27/1.03    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.27/1.03    inference(equality_resolution,[],[f50])).
% 2.27/1.03  
% 2.27/1.03  fof(f2,axiom,(
% 2.27/1.03    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.27/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/1.03  
% 2.27/1.03  fof(f45,plain,(
% 2.27/1.03    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.27/1.03    inference(cnf_transformation,[],[f2])).
% 2.27/1.03  
% 2.27/1.03  fof(f1,axiom,(
% 2.27/1.03    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.27/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/1.03  
% 2.27/1.03  fof(f33,plain,(
% 2.27/1.03    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.27/1.03    inference(nnf_transformation,[],[f1])).
% 2.27/1.03  
% 2.27/1.03  fof(f34,plain,(
% 2.27/1.03    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.27/1.03    inference(flattening,[],[f33])).
% 2.27/1.03  
% 2.27/1.03  fof(f44,plain,(
% 2.27/1.03    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.27/1.03    inference(cnf_transformation,[],[f34])).
% 2.27/1.03  
% 2.27/1.03  fof(f9,axiom,(
% 2.27/1.03    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.27/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/1.03  
% 2.27/1.03  fof(f23,plain,(
% 2.27/1.03    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.27/1.03    inference(ennf_transformation,[],[f9])).
% 2.27/1.03  
% 2.27/1.03  fof(f39,plain,(
% 2.27/1.03    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.27/1.03    inference(nnf_transformation,[],[f23])).
% 2.27/1.03  
% 2.27/1.03  fof(f62,plain,(
% 2.27/1.03    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.27/1.03    inference(cnf_transformation,[],[f39])).
% 2.27/1.03  
% 2.27/1.03  fof(f15,axiom,(
% 2.27/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.27/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/1.03  
% 2.27/1.03  fof(f20,plain,(
% 2.27/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.27/1.03    inference(pure_predicate_removal,[],[f15])).
% 2.27/1.03  
% 2.27/1.03  fof(f29,plain,(
% 2.27/1.03    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.27/1.03    inference(ennf_transformation,[],[f20])).
% 2.27/1.03  
% 2.27/1.03  fof(f71,plain,(
% 2.27/1.03    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.27/1.03    inference(cnf_transformation,[],[f29])).
% 2.27/1.03  
% 2.27/1.03  fof(f17,conjecture,(
% 2.27/1.03    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.27/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/1.03  
% 2.27/1.03  fof(f18,negated_conjecture,(
% 2.27/1.03    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.27/1.03    inference(negated_conjecture,[],[f17])).
% 2.27/1.03  
% 2.27/1.03  fof(f19,plain,(
% 2.27/1.03    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.27/1.03    inference(pure_predicate_removal,[],[f18])).
% 2.27/1.03  
% 2.27/1.03  fof(f31,plain,(
% 2.27/1.03    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 2.27/1.03    inference(ennf_transformation,[],[f19])).
% 2.27/1.03  
% 2.27/1.03  fof(f32,plain,(
% 2.27/1.03    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 2.27/1.03    inference(flattening,[],[f31])).
% 2.27/1.03  
% 2.27/1.03  fof(f40,plain,(
% 2.27/1.03    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3))),
% 2.27/1.03    introduced(choice_axiom,[])).
% 2.27/1.03  
% 2.27/1.03  fof(f41,plain,(
% 2.27/1.03    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3)),
% 2.27/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f32,f40])).
% 2.27/1.03  
% 2.27/1.03  fof(f74,plain,(
% 2.27/1.03    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 2.27/1.03    inference(cnf_transformation,[],[f41])).
% 2.27/1.03  
% 2.27/1.03  fof(f3,axiom,(
% 2.27/1.03    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.27/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/1.03  
% 2.27/1.03  fof(f46,plain,(
% 2.27/1.03    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.27/1.03    inference(cnf_transformation,[],[f3])).
% 2.27/1.03  
% 2.27/1.03  fof(f4,axiom,(
% 2.27/1.03    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.27/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/1.03  
% 2.27/1.03  fof(f47,plain,(
% 2.27/1.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.27/1.03    inference(cnf_transformation,[],[f4])).
% 2.27/1.03  
% 2.27/1.03  fof(f5,axiom,(
% 2.27/1.03    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.27/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/1.03  
% 2.27/1.03  fof(f48,plain,(
% 2.27/1.03    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.27/1.03    inference(cnf_transformation,[],[f5])).
% 2.27/1.03  
% 2.27/1.03  fof(f77,plain,(
% 2.27/1.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.27/1.03    inference(definition_unfolding,[],[f47,f48])).
% 2.27/1.03  
% 2.27/1.03  fof(f78,plain,(
% 2.27/1.03    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.27/1.03    inference(definition_unfolding,[],[f46,f77])).
% 2.27/1.03  
% 2.27/1.03  fof(f90,plain,(
% 2.27/1.03    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 2.27/1.03    inference(definition_unfolding,[],[f74,f78])).
% 2.27/1.03  
% 2.27/1.03  fof(f8,axiom,(
% 2.27/1.03    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.27/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/1.03  
% 2.27/1.03  fof(f22,plain,(
% 2.27/1.03    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.27/1.03    inference(ennf_transformation,[],[f8])).
% 2.27/1.03  
% 2.27/1.03  fof(f61,plain,(
% 2.27/1.03    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.27/1.03    inference(cnf_transformation,[],[f22])).
% 2.27/1.03  
% 2.27/1.03  fof(f7,axiom,(
% 2.27/1.03    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> ~(k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3))),
% 2.27/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/1.04  
% 2.27/1.04  fof(f21,plain,(
% 2.27/1.04    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3))),
% 2.27/1.04    inference(ennf_transformation,[],[f7])).
% 2.27/1.04  
% 2.27/1.04  fof(f37,plain,(
% 2.27/1.04    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & ((k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3) | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 2.27/1.04    inference(nnf_transformation,[],[f21])).
% 2.27/1.04  
% 2.27/1.04  fof(f38,plain,(
% 2.27/1.04    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 2.27/1.04    inference(flattening,[],[f37])).
% 2.27/1.04  
% 2.27/1.04  fof(f52,plain,(
% 2.27/1.04    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))) )),
% 2.27/1.04    inference(cnf_transformation,[],[f38])).
% 2.27/1.04  
% 2.27/1.04  fof(f87,plain,(
% 2.27/1.04    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X0,X1,X2) = X3 | k2_enumset1(X0,X0,X0,X2) = X3 | k2_enumset1(X1,X1,X1,X2) = X3 | k2_enumset1(X0,X0,X0,X1) = X3 | k2_enumset1(X2,X2,X2,X2) = X3 | k2_enumset1(X1,X1,X1,X1) = X3 | k2_enumset1(X0,X0,X0,X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k2_enumset1(X0,X0,X1,X2))) )),
% 2.27/1.04    inference(definition_unfolding,[],[f52,f48,f77,f77,f77,f78,f78,f78,f48])).
% 2.27/1.04  
% 2.27/1.04  fof(f16,axiom,(
% 2.27/1.04    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 2.27/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/1.04  
% 2.27/1.04  fof(f30,plain,(
% 2.27/1.04    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.27/1.04    inference(ennf_transformation,[],[f16])).
% 2.27/1.04  
% 2.27/1.04  fof(f72,plain,(
% 2.27/1.04    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.27/1.04    inference(cnf_transformation,[],[f30])).
% 2.27/1.04  
% 2.27/1.04  fof(f76,plain,(
% 2.27/1.04    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 2.27/1.04    inference(cnf_transformation,[],[f41])).
% 2.27/1.04  
% 2.27/1.04  fof(f89,plain,(
% 2.27/1.04    ~r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 2.27/1.04    inference(definition_unfolding,[],[f76,f78,f78])).
% 2.27/1.04  
% 2.27/1.04  fof(f14,axiom,(
% 2.27/1.04    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 2.27/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/1.04  
% 2.27/1.04  fof(f27,plain,(
% 2.27/1.04    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.27/1.04    inference(ennf_transformation,[],[f14])).
% 2.27/1.04  
% 2.27/1.04  fof(f28,plain,(
% 2.27/1.04    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.27/1.04    inference(flattening,[],[f27])).
% 2.27/1.04  
% 2.27/1.04  fof(f70,plain,(
% 2.27/1.04    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.27/1.04    inference(cnf_transformation,[],[f28])).
% 2.27/1.04  
% 2.27/1.04  fof(f88,plain,(
% 2.27/1.04    ( ! [X0,X1] : (k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1) | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.27/1.04    inference(definition_unfolding,[],[f70,f78,f78])).
% 2.27/1.04  
% 2.27/1.04  fof(f73,plain,(
% 2.27/1.04    v1_funct_1(sK3)),
% 2.27/1.04    inference(cnf_transformation,[],[f41])).
% 2.27/1.04  
% 2.27/1.04  fof(f13,axiom,(
% 2.27/1.04    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 2.27/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/1.04  
% 2.27/1.04  fof(f25,plain,(
% 2.27/1.04    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.27/1.04    inference(ennf_transformation,[],[f13])).
% 2.27/1.04  
% 2.27/1.04  fof(f26,plain,(
% 2.27/1.04    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.27/1.04    inference(flattening,[],[f25])).
% 2.27/1.04  
% 2.27/1.04  fof(f68,plain,(
% 2.27/1.04    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.27/1.04    inference(cnf_transformation,[],[f26])).
% 2.27/1.04  
% 2.27/1.04  cnf(c_21,plain,
% 2.27/1.04      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.27/1.04      inference(cnf_transformation,[],[f67]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_20,plain,
% 2.27/1.04      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 2.27/1.04      inference(cnf_transformation,[],[f65]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_840,plain,
% 2.27/1.04      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) = iProver_top
% 2.27/1.04      | v1_relat_1(X0) != iProver_top ),
% 2.27/1.04      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_2149,plain,
% 2.27/1.04      ( r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0) = iProver_top
% 2.27/1.04      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 2.27/1.04      inference(superposition,[status(thm)],[c_21,c_840]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_19,plain,
% 2.27/1.04      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.27/1.04      inference(cnf_transformation,[],[f64]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_53,plain,
% 2.27/1.04      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 2.27/1.04      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_55,plain,
% 2.27/1.04      ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 2.27/1.04      inference(instantiation,[status(thm)],[c_53]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_6,plain,
% 2.27/1.04      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 2.27/1.04      | k1_xboole_0 = X1
% 2.27/1.04      | k1_xboole_0 = X0 ),
% 2.27/1.04      inference(cnf_transformation,[],[f49]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_78,plain,
% 2.27/1.04      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.27/1.04      | k1_xboole_0 = k1_xboole_0 ),
% 2.27/1.04      inference(instantiation,[status(thm)],[c_6]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_5,plain,
% 2.27/1.04      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.27/1.04      inference(cnf_transformation,[],[f94]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_79,plain,
% 2.27/1.04      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.27/1.04      inference(instantiation,[status(thm)],[c_5]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_507,plain,
% 2.27/1.04      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 2.27/1.04      theory(equality) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_1035,plain,
% 2.27/1.04      ( v1_relat_1(X0)
% 2.27/1.04      | ~ v1_relat_1(k2_zfmisc_1(X1,X2))
% 2.27/1.04      | X0 != k2_zfmisc_1(X1,X2) ),
% 2.27/1.04      inference(instantiation,[status(thm)],[c_507]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_1036,plain,
% 2.27/1.04      ( X0 != k2_zfmisc_1(X1,X2)
% 2.27/1.04      | v1_relat_1(X0) = iProver_top
% 2.27/1.04      | v1_relat_1(k2_zfmisc_1(X1,X2)) != iProver_top ),
% 2.27/1.04      inference(predicate_to_equality,[status(thm)],[c_1035]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_1038,plain,
% 2.27/1.04      ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 2.27/1.04      | v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
% 2.27/1.04      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 2.27/1.04      inference(instantiation,[status(thm)],[c_1036]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_503,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_1169,plain,
% 2.27/1.04      ( X0 != X1 | X0 = k2_zfmisc_1(X2,X3) | k2_zfmisc_1(X2,X3) != X1 ),
% 2.27/1.04      inference(instantiation,[status(thm)],[c_503]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_1170,plain,
% 2.27/1.04      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.27/1.04      | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 2.27/1.04      | k1_xboole_0 != k1_xboole_0 ),
% 2.27/1.04      inference(instantiation,[status(thm)],[c_1169]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_2226,plain,
% 2.27/1.04      ( r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0) = iProver_top ),
% 2.27/1.04      inference(global_propositional_subsumption,
% 2.27/1.04                [status(thm)],
% 2.27/1.04                [c_2149,c_55,c_78,c_79,c_1038,c_1170]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_3,plain,
% 2.27/1.04      ( r1_tarski(k1_xboole_0,X0) ),
% 2.27/1.04      inference(cnf_transformation,[],[f45]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_851,plain,
% 2.27/1.04      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.27/1.04      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_0,plain,
% 2.27/1.04      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.27/1.04      inference(cnf_transformation,[],[f44]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_853,plain,
% 2.27/1.04      ( X0 = X1
% 2.27/1.04      | r1_tarski(X0,X1) != iProver_top
% 2.27/1.04      | r1_tarski(X1,X0) != iProver_top ),
% 2.27/1.04      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_2238,plain,
% 2.27/1.04      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.27/1.04      inference(superposition,[status(thm)],[c_851,c_853]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_2437,plain,
% 2.27/1.04      ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.27/1.04      inference(superposition,[status(thm)],[c_2226,c_2238]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_18,plain,
% 2.27/1.04      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 2.27/1.04      inference(cnf_transformation,[],[f62]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_26,plain,
% 2.27/1.04      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.27/1.04      inference(cnf_transformation,[],[f71]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_30,negated_conjecture,
% 2.27/1.04      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
% 2.27/1.04      inference(cnf_transformation,[],[f90]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_326,plain,
% 2.27/1.04      ( v4_relat_1(X0,X1)
% 2.27/1.04      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 2.27/1.04      | sK3 != X0 ),
% 2.27/1.04      inference(resolution_lifted,[status(thm)],[c_26,c_30]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_327,plain,
% 2.27/1.04      ( v4_relat_1(sK3,X0)
% 2.27/1.04      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.27/1.04      inference(unflattening,[status(thm)],[c_326]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_348,plain,
% 2.27/1.04      ( r1_tarski(k1_relat_1(X0),X1)
% 2.27/1.04      | ~ v1_relat_1(X0)
% 2.27/1.04      | X2 != X1
% 2.27/1.04      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
% 2.27/1.04      | sK3 != X0 ),
% 2.27/1.04      inference(resolution_lifted,[status(thm)],[c_18,c_327]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_349,plain,
% 2.27/1.04      ( r1_tarski(k1_relat_1(sK3),X0)
% 2.27/1.04      | ~ v1_relat_1(sK3)
% 2.27/1.04      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.27/1.04      inference(unflattening,[status(thm)],[c_348]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_834,plain,
% 2.27/1.04      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.27/1.04      | r1_tarski(k1_relat_1(sK3),X0) = iProver_top
% 2.27/1.04      | v1_relat_1(sK3) != iProver_top ),
% 2.27/1.04      inference(predicate_to_equality,[status(thm)],[c_349]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_350,plain,
% 2.27/1.04      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.27/1.04      | r1_tarski(k1_relat_1(sK3),X0) = iProver_top
% 2.27/1.04      | v1_relat_1(sK3) != iProver_top ),
% 2.27/1.04      inference(predicate_to_equality,[status(thm)],[c_349]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_16,plain,
% 2.27/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 2.27/1.04      inference(cnf_transformation,[],[f61]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_302,plain,
% 2.27/1.04      ( ~ v1_relat_1(X0)
% 2.27/1.04      | v1_relat_1(X1)
% 2.27/1.04      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(X0)
% 2.27/1.04      | sK3 != X1 ),
% 2.27/1.04      inference(resolution_lifted,[status(thm)],[c_16,c_30]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_303,plain,
% 2.27/1.04      ( ~ v1_relat_1(X0)
% 2.27/1.04      | v1_relat_1(sK3)
% 2.27/1.04      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(X0) ),
% 2.27/1.04      inference(unflattening,[status(thm)],[c_302]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_997,plain,
% 2.27/1.04      ( ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 2.27/1.04      | v1_relat_1(sK3)
% 2.27/1.04      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.27/1.04      inference(instantiation,[status(thm)],[c_303]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_998,plain,
% 2.27/1.04      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.27/1.04      | v1_relat_1(k2_zfmisc_1(X0,X1)) != iProver_top
% 2.27/1.04      | v1_relat_1(sK3) = iProver_top ),
% 2.27/1.04      inference(predicate_to_equality,[status(thm)],[c_997]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_1118,plain,
% 2.27/1.04      ( r1_tarski(k1_relat_1(sK3),X0) = iProver_top
% 2.27/1.04      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.27/1.04      inference(global_propositional_subsumption,
% 2.27/1.04                [status(thm)],
% 2.27/1.04                [c_834,c_53,c_350,c_998]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_1119,plain,
% 2.27/1.04      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.27/1.04      | r1_tarski(k1_relat_1(sK3),X0) = iProver_top ),
% 2.27/1.04      inference(renaming,[status(thm)],[c_1118]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_1126,plain,
% 2.27/1.04      ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0)) = iProver_top ),
% 2.27/1.04      inference(equality_resolution,[status(thm)],[c_1119]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_15,plain,
% 2.27/1.04      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X2,X3))
% 2.27/1.04      | k2_enumset1(X1,X1,X2,X3) = X0
% 2.27/1.04      | k2_enumset1(X1,X1,X1,X3) = X0
% 2.27/1.04      | k2_enumset1(X2,X2,X2,X3) = X0
% 2.27/1.04      | k2_enumset1(X1,X1,X1,X2) = X0
% 2.27/1.04      | k2_enumset1(X3,X3,X3,X3) = X0
% 2.27/1.04      | k2_enumset1(X2,X2,X2,X2) = X0
% 2.27/1.04      | k2_enumset1(X1,X1,X1,X1) = X0
% 2.27/1.04      | k1_xboole_0 = X0 ),
% 2.27/1.04      inference(cnf_transformation,[],[f87]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_842,plain,
% 2.27/1.04      ( k2_enumset1(X0,X0,X1,X2) = X3
% 2.27/1.04      | k2_enumset1(X0,X0,X0,X2) = X3
% 2.27/1.04      | k2_enumset1(X1,X1,X1,X2) = X3
% 2.27/1.04      | k2_enumset1(X0,X0,X0,X1) = X3
% 2.27/1.04      | k2_enumset1(X2,X2,X2,X2) = X3
% 2.27/1.04      | k2_enumset1(X1,X1,X1,X1) = X3
% 2.27/1.04      | k2_enumset1(X0,X0,X0,X0) = X3
% 2.27/1.04      | k1_xboole_0 = X3
% 2.27/1.04      | r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) != iProver_top ),
% 2.27/1.04      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_2427,plain,
% 2.27/1.04      ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
% 2.27/1.04      | k1_relat_1(sK3) = k1_xboole_0 ),
% 2.27/1.04      inference(superposition,[status(thm)],[c_1126,c_842]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_27,plain,
% 2.27/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.27/1.04      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 2.27/1.04      inference(cnf_transformation,[],[f72]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_317,plain,
% 2.27/1.04      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 2.27/1.04      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.27/1.04      | sK3 != X2 ),
% 2.27/1.04      inference(resolution_lifted,[status(thm)],[c_27,c_30]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_318,plain,
% 2.27/1.04      ( k7_relset_1(X0,X1,sK3,X2) = k9_relat_1(sK3,X2)
% 2.27/1.04      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.27/1.04      inference(unflattening,[status(thm)],[c_317]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_2501,plain,
% 2.27/1.04      ( k7_relset_1(X0,X1,sK3,X2) = k9_relat_1(sK3,X2)
% 2.27/1.04      | k1_relat_1(sK3) = k1_xboole_0
% 2.27/1.04      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.27/1.04      inference(superposition,[status(thm)],[c_2427,c_318]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_28,negated_conjecture,
% 2.27/1.04      ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
% 2.27/1.04      inference(cnf_transformation,[],[f89]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_502,plain,( X0 = X0 ),theory(equality) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_1002,plain,
% 2.27/1.04      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) = k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
% 2.27/1.04      inference(instantiation,[status(thm)],[c_502]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_835,plain,
% 2.27/1.04      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(X0)
% 2.27/1.04      | v1_relat_1(X0) != iProver_top
% 2.27/1.04      | v1_relat_1(sK3) = iProver_top ),
% 2.27/1.04      inference(predicate_to_equality,[status(thm)],[c_303]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_1046,plain,
% 2.27/1.04      ( v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != iProver_top
% 2.27/1.04      | v1_relat_1(sK3) = iProver_top ),
% 2.27/1.04      inference(equality_resolution,[status(thm)],[c_835]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_1047,plain,
% 2.27/1.04      ( ~ v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
% 2.27/1.04      | v1_relat_1(sK3) ),
% 2.27/1.04      inference(predicate_to_equality_rev,[status(thm)],[c_1046]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_1003,plain,
% 2.27/1.04      ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0)
% 2.27/1.04      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
% 2.27/1.04      inference(instantiation,[status(thm)],[c_318]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_1103,plain,
% 2.27/1.04      ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) = k9_relat_1(sK3,sK2)
% 2.27/1.04      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
% 2.27/1.04      inference(instantiation,[status(thm)],[c_1003]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_1311,plain,
% 2.27/1.04      ( v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
% 2.27/1.04      inference(instantiation,[status(thm)],[c_19]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_1312,plain,
% 2.27/1.04      ( v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) = iProver_top ),
% 2.27/1.04      inference(predicate_to_equality,[status(thm)],[c_1311]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_1399,plain,
% 2.27/1.04      ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | ~ v1_relat_1(sK3) ),
% 2.27/1.04      inference(instantiation,[status(thm)],[c_20]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_504,plain,
% 2.27/1.04      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.27/1.04      theory(equality) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_1048,plain,
% 2.27/1.04      ( ~ r1_tarski(X0,X1)
% 2.27/1.04      | r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 2.27/1.04      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != X0
% 2.27/1.04      | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X1 ),
% 2.27/1.04      inference(instantiation,[status(thm)],[c_504]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_1104,plain,
% 2.27/1.04      ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 2.27/1.04      | ~ r1_tarski(k9_relat_1(sK3,sK2),X0)
% 2.27/1.04      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
% 2.27/1.04      | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X0 ),
% 2.27/1.04      inference(instantiation,[status(thm)],[c_1048]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_1400,plain,
% 2.27/1.04      ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 2.27/1.04      | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
% 2.27/1.04      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
% 2.27/1.04      | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k2_relat_1(sK3) ),
% 2.27/1.04      inference(instantiation,[status(thm)],[c_1104]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_25,plain,
% 2.27/1.04      ( ~ v1_funct_1(X0)
% 2.27/1.04      | ~ v1_relat_1(X0)
% 2.27/1.04      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 2.27/1.04      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
% 2.27/1.04      inference(cnf_transformation,[],[f88]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_31,negated_conjecture,
% 2.27/1.04      ( v1_funct_1(sK3) ),
% 2.27/1.04      inference(cnf_transformation,[],[f73]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_283,plain,
% 2.27/1.04      ( ~ v1_relat_1(X0)
% 2.27/1.04      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 2.27/1.04      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
% 2.27/1.04      | sK3 != X0 ),
% 2.27/1.04      inference(resolution_lifted,[status(thm)],[c_25,c_31]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_284,plain,
% 2.27/1.04      ( ~ v1_relat_1(sK3)
% 2.27/1.04      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
% 2.27/1.04      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
% 2.27/1.04      inference(unflattening,[status(thm)],[c_283]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_836,plain,
% 2.27/1.04      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
% 2.27/1.04      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
% 2.27/1.04      | v1_relat_1(sK3) != iProver_top ),
% 2.27/1.04      inference(predicate_to_equality,[status(thm)],[c_284]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_2489,plain,
% 2.27/1.04      ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
% 2.27/1.04      | k1_relat_1(sK3) = k1_xboole_0
% 2.27/1.04      | v1_relat_1(sK3) != iProver_top ),
% 2.27/1.04      inference(superposition,[status(thm)],[c_2427,c_836]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_2722,plain,
% 2.27/1.04      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 2.27/1.04      inference(global_propositional_subsumption,
% 2.27/1.04                [status(thm)],
% 2.27/1.04                [c_2501,c_28,c_1002,c_1046,c_1047,c_1103,c_1311,c_1312,
% 2.27/1.04                 c_1399,c_1400,c_2489]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_24,plain,
% 2.27/1.04      ( ~ v1_relat_1(X0) | k1_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 2.27/1.04      inference(cnf_transformation,[],[f68]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_838,plain,
% 2.27/1.04      ( k1_relat_1(X0) != k1_xboole_0
% 2.27/1.04      | k1_xboole_0 = X0
% 2.27/1.04      | v1_relat_1(X0) != iProver_top ),
% 2.27/1.04      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_2746,plain,
% 2.27/1.04      ( sK3 = k1_xboole_0 | v1_relat_1(sK3) != iProver_top ),
% 2.27/1.04      inference(superposition,[status(thm)],[c_2722,c_838]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_2749,plain,
% 2.27/1.04      ( sK3 = k1_xboole_0 ),
% 2.27/1.04      inference(global_propositional_subsumption,
% 2.27/1.04                [status(thm)],
% 2.27/1.04                [c_2746,c_1046,c_1312]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_995,plain,
% 2.27/1.04      ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
% 2.27/1.04      inference(equality_resolution,[status(thm)],[c_318]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_837,plain,
% 2.27/1.04      ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 2.27/1.04      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_1021,plain,
% 2.27/1.04      ( r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 2.27/1.04      inference(demodulation,[status(thm)],[c_995,c_837]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_2758,plain,
% 2.27/1.04      ( r1_tarski(k9_relat_1(k1_xboole_0,sK2),k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.27/1.04      inference(demodulation,[status(thm)],[c_2749,c_1021]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_3386,plain,
% 2.27/1.04      ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.27/1.04      inference(demodulation,[status(thm)],[c_2437,c_2758]) ).
% 2.27/1.04  
% 2.27/1.04  cnf(c_3666,plain,
% 2.27/1.04      ( $false ),
% 2.27/1.04      inference(forward_subsumption_resolution,[status(thm)],[c_3386,c_851]) ).
% 2.27/1.04  
% 2.27/1.04  
% 2.27/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 2.27/1.04  
% 2.27/1.04  ------                               Statistics
% 2.27/1.04  
% 2.27/1.04  ------ General
% 2.27/1.04  
% 2.27/1.04  abstr_ref_over_cycles:                  0
% 2.27/1.04  abstr_ref_under_cycles:                 0
% 2.27/1.04  gc_basic_clause_elim:                   0
% 2.27/1.04  forced_gc_time:                         0
% 2.27/1.04  parsing_time:                           0.012
% 2.27/1.04  unif_index_cands_time:                  0.
% 2.27/1.04  unif_index_add_time:                    0.
% 2.27/1.04  orderings_time:                         0.
% 2.27/1.04  out_proof_time:                         0.043
% 2.27/1.04  total_time:                             0.214
% 2.27/1.04  num_of_symbols:                         49
% 2.27/1.04  num_of_terms:                           3231
% 2.27/1.04  
% 2.27/1.04  ------ Preprocessing
% 2.27/1.04  
% 2.27/1.04  num_of_splits:                          0
% 2.27/1.04  num_of_split_atoms:                     0
% 2.27/1.04  num_of_reused_defs:                     0
% 2.27/1.04  num_eq_ax_congr_red:                    6
% 2.27/1.04  num_of_sem_filtered_clauses:            1
% 2.27/1.04  num_of_subtypes:                        0
% 2.27/1.04  monotx_restored_types:                  0
% 2.27/1.04  sat_num_of_epr_types:                   0
% 2.27/1.04  sat_num_of_non_cyclic_types:            0
% 2.27/1.04  sat_guarded_non_collapsed_types:        0
% 2.27/1.04  num_pure_diseq_elim:                    0
% 2.27/1.04  simp_replaced_by:                       0
% 2.27/1.04  res_preprocessed:                       137
% 2.27/1.04  prep_upred:                             0
% 2.27/1.04  prep_unflattend:                        6
% 2.27/1.04  smt_new_axioms:                         0
% 2.27/1.04  pred_elim_cands:                        2
% 2.27/1.04  pred_elim:                              3
% 2.27/1.04  pred_elim_cl:                           4
% 2.27/1.04  pred_elim_cycles:                       5
% 2.27/1.04  merged_defs:                            0
% 2.27/1.04  merged_defs_ncl:                        0
% 2.27/1.04  bin_hyper_res:                          0
% 2.27/1.04  prep_cycles:                            4
% 2.27/1.04  pred_elim_time:                         0.003
% 2.27/1.04  splitting_time:                         0.
% 2.27/1.04  sem_filter_time:                        0.
% 2.27/1.04  monotx_time:                            0.001
% 2.27/1.04  subtype_inf_time:                       0.
% 2.27/1.04  
% 2.27/1.04  ------ Problem properties
% 2.27/1.04  
% 2.27/1.04  clauses:                                27
% 2.27/1.04  conjectures:                            2
% 2.27/1.04  epr:                                    4
% 2.27/1.04  horn:                                   25
% 2.27/1.04  ground:                                 4
% 2.27/1.04  unary:                                  17
% 2.27/1.04  binary:                                 2
% 2.27/1.04  lits:                                   51
% 2.27/1.04  lits_eq:                                27
% 2.27/1.04  fd_pure:                                0
% 2.27/1.04  fd_pseudo:                              0
% 2.27/1.04  fd_cond:                                3
% 2.27/1.04  fd_pseudo_cond:                         2
% 2.27/1.04  ac_symbols:                             0
% 2.27/1.04  
% 2.27/1.04  ------ Propositional Solver
% 2.27/1.04  
% 2.27/1.04  prop_solver_calls:                      28
% 2.27/1.04  prop_fast_solver_calls:                 711
% 2.27/1.04  smt_solver_calls:                       0
% 2.27/1.04  smt_fast_solver_calls:                  0
% 2.27/1.04  prop_num_of_clauses:                    1306
% 2.27/1.04  prop_preprocess_simplified:             4855
% 2.27/1.04  prop_fo_subsumed:                       16
% 2.27/1.04  prop_solver_time:                       0.
% 2.27/1.04  smt_solver_time:                        0.
% 2.27/1.04  smt_fast_solver_time:                   0.
% 2.27/1.04  prop_fast_solver_time:                  0.
% 2.27/1.04  prop_unsat_core_time:                   0.
% 2.27/1.04  
% 2.27/1.04  ------ QBF
% 2.27/1.04  
% 2.27/1.04  qbf_q_res:                              0
% 2.27/1.04  qbf_num_tautologies:                    0
% 2.27/1.04  qbf_prep_cycles:                        0
% 2.27/1.04  
% 2.27/1.04  ------ BMC1
% 2.27/1.04  
% 2.27/1.04  bmc1_current_bound:                     -1
% 2.27/1.04  bmc1_last_solved_bound:                 -1
% 2.27/1.04  bmc1_unsat_core_size:                   -1
% 2.27/1.04  bmc1_unsat_core_parents_size:           -1
% 2.27/1.04  bmc1_merge_next_fun:                    0
% 2.27/1.04  bmc1_unsat_core_clauses_time:           0.
% 2.27/1.04  
% 2.27/1.04  ------ Instantiation
% 2.27/1.04  
% 2.27/1.04  inst_num_of_clauses:                    493
% 2.27/1.04  inst_num_in_passive:                    81
% 2.27/1.04  inst_num_in_active:                     249
% 2.27/1.04  inst_num_in_unprocessed:                163
% 2.27/1.04  inst_num_of_loops:                      270
% 2.27/1.04  inst_num_of_learning_restarts:          0
% 2.27/1.04  inst_num_moves_active_passive:          18
% 2.27/1.04  inst_lit_activity:                      0
% 2.27/1.04  inst_lit_activity_moves:                0
% 2.27/1.04  inst_num_tautologies:                   0
% 2.27/1.04  inst_num_prop_implied:                  0
% 2.27/1.04  inst_num_existing_simplified:           0
% 2.27/1.04  inst_num_eq_res_simplified:             0
% 2.27/1.04  inst_num_child_elim:                    0
% 2.27/1.04  inst_num_of_dismatching_blockings:      61
% 2.27/1.04  inst_num_of_non_proper_insts:           453
% 2.27/1.04  inst_num_of_duplicates:                 0
% 2.27/1.04  inst_inst_num_from_inst_to_res:         0
% 2.27/1.04  inst_dismatching_checking_time:         0.
% 2.27/1.04  
% 2.27/1.04  ------ Resolution
% 2.27/1.04  
% 2.27/1.04  res_num_of_clauses:                     0
% 2.27/1.04  res_num_in_passive:                     0
% 2.27/1.04  res_num_in_active:                      0
% 2.27/1.04  res_num_of_loops:                       141
% 2.27/1.04  res_forward_subset_subsumed:            77
% 2.27/1.04  res_backward_subset_subsumed:           0
% 2.27/1.04  res_forward_subsumed:                   0
% 2.27/1.04  res_backward_subsumed:                  0
% 2.27/1.04  res_forward_subsumption_resolution:     0
% 2.27/1.04  res_backward_subsumption_resolution:    0
% 2.27/1.04  res_clause_to_clause_subsumption:       247
% 2.27/1.04  res_orphan_elimination:                 0
% 2.27/1.04  res_tautology_del:                      17
% 2.27/1.04  res_num_eq_res_simplified:              0
% 2.27/1.04  res_num_sel_changes:                    0
% 2.27/1.04  res_moves_from_active_to_pass:          0
% 2.27/1.04  
% 2.27/1.04  ------ Superposition
% 2.27/1.04  
% 2.27/1.04  sup_time_total:                         0.
% 2.27/1.04  sup_time_generating:                    0.
% 2.27/1.04  sup_time_sim_full:                      0.
% 2.27/1.04  sup_time_sim_immed:                     0.
% 2.27/1.04  
% 2.27/1.04  sup_num_of_clauses:                     41
% 2.27/1.04  sup_num_in_active:                      31
% 2.27/1.04  sup_num_in_passive:                     10
% 2.27/1.04  sup_num_of_loops:                       53
% 2.27/1.04  sup_fw_superposition:                   49
% 2.27/1.04  sup_bw_superposition:                   32
% 2.27/1.04  sup_immediate_simplified:               17
% 2.27/1.04  sup_given_eliminated:                   0
% 2.27/1.04  comparisons_done:                       0
% 2.27/1.04  comparisons_avoided:                    0
% 2.27/1.04  
% 2.27/1.04  ------ Simplifications
% 2.27/1.04  
% 2.27/1.04  
% 2.27/1.04  sim_fw_subset_subsumed:                 8
% 2.27/1.04  sim_bw_subset_subsumed:                 7
% 2.27/1.04  sim_fw_subsumed:                        10
% 2.27/1.04  sim_bw_subsumed:                        0
% 2.27/1.04  sim_fw_subsumption_res:                 1
% 2.27/1.04  sim_bw_subsumption_res:                 0
% 2.27/1.04  sim_tautology_del:                      0
% 2.27/1.04  sim_eq_tautology_del:                   18
% 2.27/1.04  sim_eq_res_simp:                        0
% 2.27/1.04  sim_fw_demodulated:                     0
% 2.27/1.04  sim_bw_demodulated:                     22
% 2.27/1.04  sim_light_normalised:                   4
% 2.27/1.04  sim_joinable_taut:                      0
% 2.27/1.04  sim_joinable_simp:                      0
% 2.27/1.04  sim_ac_normalised:                      0
% 2.27/1.04  sim_smt_subsumption:                    0
% 2.27/1.04  
%------------------------------------------------------------------------------
