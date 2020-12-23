%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:52 EST 2020

% Result     : Theorem 27.94s
% Output     : CNFRefutation 27.94s
% Verified   : 
% Statistics : Number of formulae       :  230 (1587 expanded)
%              Number of clauses        :  122 ( 453 expanded)
%              Number of leaves         :   30 ( 360 expanded)
%              Depth                    :   29
%              Number of atoms          :  498 (3254 expanded)
%              Number of equality atoms :  263 (1362 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f19,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f85,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f29,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f29])).

fof(f31,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(pure_predicate_removal,[],[f30])).

fof(f47,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f48,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f47])).

fof(f57,plain,
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

fof(f58,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f48,f57])).

fof(f98,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f58])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f12])).

fof(f101,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f71,f72])).

fof(f102,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f70,f101])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f69,f102])).

fof(f104,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f68,f103])).

fof(f105,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f67,f104])).

fof(f106,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f66,f105])).

fof(f113,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f98,f106])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f49])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f114,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f60])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v4_relat_1(X1,X0)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f23,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f40])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f109,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f79,f62,f106])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f27])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f107,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f74,f106])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f61,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f43])).

fof(f94,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f111,plain,(
    ! [X0,X1] :
      ( k6_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f94,f106,f106])).

fof(f97,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f28,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f100,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f58])).

fof(f112,plain,(
    ~ r1_tarski(k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f100,f106,f106])).

fof(f22,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f88,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f52])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f117,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f76])).

fof(f24,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f91,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f24])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f116,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f77])).

fof(f92,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1566,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_18,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1557,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_1549,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1560,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2794,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1549,c_1560])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_13,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_246,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_13])).

cnf(c_247,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_246])).

cnf(c_300,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_15,c_247])).

cnf(c_1546,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_300])).

cnf(c_2880,plain,
    ( v1_relat_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2794,c_1546])).

cnf(c_3026,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1557,c_2880])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_1568,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_16,plain,
    ( v4_relat_1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1559,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4890,plain,
    ( v4_relat_1(X0,k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1568,c_1559])).

cnf(c_20,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1555,plain,
    ( k7_relat_1(X0,X1) = X0
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_9768,plain,
    ( k7_relat_1(X0,k1_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4890,c_1555])).

cnf(c_9774,plain,
    ( k7_relat_1(sK3,k1_relat_1(sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_3026,c_9768])).

cnf(c_19,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1556,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3109,plain,
    ( k2_relat_1(k7_relat_1(sK3,X0)) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_3026,c_1556])).

cnf(c_9926,plain,
    ( k9_relat_1(sK3,k1_relat_1(sK3)) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_9774,c_3109])).

cnf(c_26,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1553,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2738,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1553,c_1546])).

cnf(c_8719,plain,
    ( k2_relat_1(k7_relat_1(k7_relat_1(X0,X1),X2)) = k9_relat_1(k7_relat_1(X0,X1),X2)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2738,c_1556])).

cnf(c_17961,plain,
    ( k2_relat_1(k7_relat_1(k7_relat_1(sK3,X0),X1)) = k9_relat_1(k7_relat_1(sK3,X0),X1) ),
    inference(superposition,[status(thm)],[c_3026,c_8719])).

cnf(c_22,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_176,plain,
    ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_22,c_15,c_13])).

cnf(c_177,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_176])).

cnf(c_1547,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_177])).

cnf(c_3112,plain,
    ( r1_tarski(X0,k7_relat_1(sK3,X1)) != iProver_top
    | r1_tarski(k2_relat_1(X0),k9_relat_1(sK3,X1)) = iProver_top
    | v1_relat_1(k7_relat_1(sK3,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3109,c_1547])).

cnf(c_18247,plain,
    ( r1_tarski(k9_relat_1(k7_relat_1(sK3,X0),X1),k9_relat_1(sK3,X2)) = iProver_top
    | r1_tarski(k7_relat_1(k7_relat_1(sK3,X0),X1),k7_relat_1(sK3,X2)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_17961,c_3112])).

cnf(c_19222,plain,
    ( r1_tarski(k9_relat_1(k7_relat_1(sK3,X0),X1),k9_relat_1(sK3,X0)) = iProver_top
    | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1553,c_18247])).

cnf(c_3911,plain,
    ( ~ r1_tarski(X0,sK3)
    | v1_relat_1(X0)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_300])).

cnf(c_4157,plain,
    ( ~ r1_tarski(k7_relat_1(sK3,X0),sK3)
    | v1_relat_1(k7_relat_1(sK3,X0))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_3911])).

cnf(c_4158,plain,
    ( r1_tarski(k7_relat_1(sK3,X0),sK3) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4157])).

cnf(c_7422,plain,
    ( r1_tarski(k7_relat_1(sK3,X0),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_7423,plain,
    ( r1_tarski(k7_relat_1(sK3,X0),sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7422])).

cnf(c_21823,plain,
    ( r1_tarski(k9_relat_1(k7_relat_1(sK3,X0),X1),k9_relat_1(sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19222,c_3026,c_4158,c_7423])).

cnf(c_21832,plain,
    ( r1_tarski(k9_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)),X0),k2_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9926,c_21823])).

cnf(c_21841,plain,
    ( r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_21832,c_9774])).

cnf(c_11,plain,
    ( r2_hidden(X0,X1)
    | k5_xboole_0(X1,k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X1 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1563,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = X0
    | r2_hidden(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_28,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1552,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3413,plain,
    ( v4_relat_1(sK3,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1549,c_1552])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1565,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_17,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1558,plain,
    ( v4_relat_1(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1569,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4025,plain,
    ( k1_relat_1(X0) = X1
    | v4_relat_1(X0,X1) != iProver_top
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1558,c_1569])).

cnf(c_20867,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_relat_1(X1)
    | v4_relat_1(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top
    | r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1565,c_4025])).

cnf(c_106254,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | r2_hidden(sK0,k1_relat_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3413,c_20867])).

cnf(c_106532,plain,
    ( r2_hidden(sK0,k1_relat_1(sK3)) != iProver_top
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_106254,c_3026])).

cnf(c_106533,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | r2_hidden(sK0,k1_relat_1(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_106532])).

cnf(c_106536,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k5_xboole_0(k1_relat_1(sK3),k3_xboole_0(k1_relat_1(sK3),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1563,c_106533])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1567,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4026,plain,
    ( k3_xboole_0(k1_relat_1(X0),X1) = k1_relat_1(X0)
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1558,c_1567])).

cnf(c_22699,plain,
    ( k3_xboole_0(k1_relat_1(sK3),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3413,c_4026])).

cnf(c_23073,plain,
    ( k3_xboole_0(k1_relat_1(sK3),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_22699,c_3026])).

cnf(c_106537,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k5_xboole_0(k1_relat_1(sK3),k1_relat_1(sK3)) = k1_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_106536,c_23073])).

cnf(c_5,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_106538,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_106537,c_5])).

cnf(c_27,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k1_relat_1(X0)
    | k6_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_395,plain,
    ( ~ v1_relat_1(X0)
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k1_relat_1(X0)
    | k6_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_33])).

cnf(c_396,plain,
    ( ~ v1_relat_1(sK3)
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(sK3)
    | k6_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_395])).

cnf(c_1545,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(sK3)
    | k6_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_396])).

cnf(c_106713,plain,
    ( k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_106538,c_1545])).

cnf(c_107201,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_106713,c_3026])).

cnf(c_107202,plain,
    ( k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_107201])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1551,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4180,plain,
    ( k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1549,c_1551])).

cnf(c_30,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1550,plain,
    ( r1_tarski(k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_4343,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4180,c_1550])).

cnf(c_107221,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_107202,c_4343])).

cnf(c_107591,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_21841,c_107221])).

cnf(c_21,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1554,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3480,plain,
    ( r1_tarski(k7_relat_1(sK3,X0),k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),k9_relat_1(sK3,X0))) = iProver_top
    | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3109,c_1554])).

cnf(c_3707,plain,
    ( k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),k9_relat_1(sK3,X0)) = k7_relat_1(sK3,X0)
    | r1_tarski(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),k9_relat_1(sK3,X0)),k7_relat_1(sK3,X0)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3480,c_1569])).

cnf(c_14146,plain,
    ( r1_tarski(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),k9_relat_1(sK3,X0)),k7_relat_1(sK3,X0)) != iProver_top
    | k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),k9_relat_1(sK3,X0)) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3707,c_3026,c_4158,c_7423])).

cnf(c_14147,plain,
    ( k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),k9_relat_1(sK3,X0)) = k7_relat_1(sK3,X0)
    | r1_tarski(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),k9_relat_1(sK3,X0)),k7_relat_1(sK3,X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_14146])).

cnf(c_14157,plain,
    ( k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3))),k9_relat_1(sK3,k1_relat_1(sK3))) = k7_relat_1(sK3,k1_relat_1(sK3))
    | r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),k9_relat_1(sK3,k1_relat_1(sK3))),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_9774,c_14147])).

cnf(c_14158,plain,
    ( k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)) = sK3
    | r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)),sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14157,c_9774,c_9926])).

cnf(c_108033,plain,
    ( k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3)) = sK3
    | r1_tarski(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3)),sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_107591,c_14158])).

cnf(c_9,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f117])).

cnf(c_108047,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_108033,c_9])).

cnf(c_24480,plain,
    ( r1_tarski(k1_xboole_0,sK3) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_24481,plain,
    ( r1_tarski(k1_xboole_0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24480])).

cnf(c_109036,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_108047,c_24481])).

cnf(c_109412,plain,
    ( r1_tarski(k9_relat_1(k1_xboole_0,sK2),k6_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_109036,c_4343])).

cnf(c_25,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_4894,plain,
    ( v4_relat_1(k1_xboole_0,X0) = iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_25,c_1559])).

cnf(c_96,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_8,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f116])).

cnf(c_2297,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_1557])).

cnf(c_4960,plain,
    ( v4_relat_1(k1_xboole_0,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4894,c_96,c_2297])).

cnf(c_4966,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4960,c_1555])).

cnf(c_4222,plain,
    ( ~ v4_relat_1(k1_xboole_0,X0)
    | ~ v1_relat_1(k1_xboole_0)
    | k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_4223,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
    | v4_relat_1(k1_xboole_0,X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4222])).

cnf(c_7945,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4966,c_96,c_2297,c_4223,c_4894])).

cnf(c_2875,plain,
    ( k2_relat_1(k7_relat_1(k1_xboole_0,X0)) = k9_relat_1(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_2297,c_1556])).

cnf(c_7954,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_7945,c_2875])).

cnf(c_24,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_7955,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7954,c_24])).

cnf(c_109436,plain,
    ( r1_tarski(k1_xboole_0,k6_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_109412,c_7955])).

cnf(c_110456,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_1566,c_109436])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:11:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 27.94/3.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.94/3.98  
% 27.94/3.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.94/3.98  
% 27.94/3.98  ------  iProver source info
% 27.94/3.98  
% 27.94/3.98  git: date: 2020-06-30 10:37:57 +0100
% 27.94/3.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.94/3.98  git: non_committed_changes: false
% 27.94/3.98  git: last_make_outside_of_git: false
% 27.94/3.98  
% 27.94/3.98  ------ 
% 27.94/3.98  
% 27.94/3.98  ------ Input Options
% 27.94/3.98  
% 27.94/3.98  --out_options                           all
% 27.94/3.98  --tptp_safe_out                         true
% 27.94/3.98  --problem_path                          ""
% 27.94/3.98  --include_path                          ""
% 27.94/3.98  --clausifier                            res/vclausify_rel
% 27.94/3.98  --clausifier_options                    ""
% 27.94/3.98  --stdin                                 false
% 27.94/3.98  --stats_out                             all
% 27.94/3.98  
% 27.94/3.98  ------ General Options
% 27.94/3.98  
% 27.94/3.98  --fof                                   false
% 27.94/3.98  --time_out_real                         305.
% 27.94/3.98  --time_out_virtual                      -1.
% 27.94/3.98  --symbol_type_check                     false
% 27.94/3.98  --clausify_out                          false
% 27.94/3.98  --sig_cnt_out                           false
% 27.94/3.98  --trig_cnt_out                          false
% 27.94/3.98  --trig_cnt_out_tolerance                1.
% 27.94/3.98  --trig_cnt_out_sk_spl                   false
% 27.94/3.98  --abstr_cl_out                          false
% 27.94/3.98  
% 27.94/3.98  ------ Global Options
% 27.94/3.98  
% 27.94/3.98  --schedule                              default
% 27.94/3.98  --add_important_lit                     false
% 27.94/3.98  --prop_solver_per_cl                    1000
% 27.94/3.98  --min_unsat_core                        false
% 27.94/3.98  --soft_assumptions                      false
% 27.94/3.98  --soft_lemma_size                       3
% 27.94/3.98  --prop_impl_unit_size                   0
% 27.94/3.98  --prop_impl_unit                        []
% 27.94/3.98  --share_sel_clauses                     true
% 27.94/3.98  --reset_solvers                         false
% 27.94/3.98  --bc_imp_inh                            [conj_cone]
% 27.94/3.98  --conj_cone_tolerance                   3.
% 27.94/3.98  --extra_neg_conj                        none
% 27.94/3.98  --large_theory_mode                     true
% 27.94/3.98  --prolific_symb_bound                   200
% 27.94/3.98  --lt_threshold                          2000
% 27.94/3.98  --clause_weak_htbl                      true
% 27.94/3.98  --gc_record_bc_elim                     false
% 27.94/3.98  
% 27.94/3.98  ------ Preprocessing Options
% 27.94/3.98  
% 27.94/3.98  --preprocessing_flag                    true
% 27.94/3.98  --time_out_prep_mult                    0.1
% 27.94/3.98  --splitting_mode                        input
% 27.94/3.98  --splitting_grd                         true
% 27.94/3.98  --splitting_cvd                         false
% 27.94/3.98  --splitting_cvd_svl                     false
% 27.94/3.98  --splitting_nvd                         32
% 27.94/3.98  --sub_typing                            true
% 27.94/3.98  --prep_gs_sim                           true
% 27.94/3.98  --prep_unflatten                        true
% 27.94/3.98  --prep_res_sim                          true
% 27.94/3.98  --prep_upred                            true
% 27.94/3.98  --prep_sem_filter                       exhaustive
% 27.94/3.98  --prep_sem_filter_out                   false
% 27.94/3.98  --pred_elim                             true
% 27.94/3.98  --res_sim_input                         true
% 27.94/3.98  --eq_ax_congr_red                       true
% 27.94/3.98  --pure_diseq_elim                       true
% 27.94/3.98  --brand_transform                       false
% 27.94/3.98  --non_eq_to_eq                          false
% 27.94/3.98  --prep_def_merge                        true
% 27.94/3.98  --prep_def_merge_prop_impl              false
% 27.94/3.98  --prep_def_merge_mbd                    true
% 27.94/3.98  --prep_def_merge_tr_red                 false
% 27.94/3.98  --prep_def_merge_tr_cl                  false
% 27.94/3.98  --smt_preprocessing                     true
% 27.94/3.98  --smt_ac_axioms                         fast
% 27.94/3.98  --preprocessed_out                      false
% 27.94/3.98  --preprocessed_stats                    false
% 27.94/3.98  
% 27.94/3.98  ------ Abstraction refinement Options
% 27.94/3.98  
% 27.94/3.98  --abstr_ref                             []
% 27.94/3.98  --abstr_ref_prep                        false
% 27.94/3.98  --abstr_ref_until_sat                   false
% 27.94/3.98  --abstr_ref_sig_restrict                funpre
% 27.94/3.98  --abstr_ref_af_restrict_to_split_sk     false
% 27.94/3.98  --abstr_ref_under                       []
% 27.94/3.98  
% 27.94/3.98  ------ SAT Options
% 27.94/3.98  
% 27.94/3.98  --sat_mode                              false
% 27.94/3.98  --sat_fm_restart_options                ""
% 27.94/3.98  --sat_gr_def                            false
% 27.94/3.98  --sat_epr_types                         true
% 27.94/3.98  --sat_non_cyclic_types                  false
% 27.94/3.98  --sat_finite_models                     false
% 27.94/3.98  --sat_fm_lemmas                         false
% 27.94/3.98  --sat_fm_prep                           false
% 27.94/3.98  --sat_fm_uc_incr                        true
% 27.94/3.98  --sat_out_model                         small
% 27.94/3.98  --sat_out_clauses                       false
% 27.94/3.98  
% 27.94/3.98  ------ QBF Options
% 27.94/3.98  
% 27.94/3.98  --qbf_mode                              false
% 27.94/3.98  --qbf_elim_univ                         false
% 27.94/3.98  --qbf_dom_inst                          none
% 27.94/3.98  --qbf_dom_pre_inst                      false
% 27.94/3.98  --qbf_sk_in                             false
% 27.94/3.98  --qbf_pred_elim                         true
% 27.94/3.98  --qbf_split                             512
% 27.94/3.98  
% 27.94/3.98  ------ BMC1 Options
% 27.94/3.98  
% 27.94/3.98  --bmc1_incremental                      false
% 27.94/3.98  --bmc1_axioms                           reachable_all
% 27.94/3.98  --bmc1_min_bound                        0
% 27.94/3.98  --bmc1_max_bound                        -1
% 27.94/3.98  --bmc1_max_bound_default                -1
% 27.94/3.98  --bmc1_symbol_reachability              true
% 27.94/3.98  --bmc1_property_lemmas                  false
% 27.94/3.98  --bmc1_k_induction                      false
% 27.94/3.98  --bmc1_non_equiv_states                 false
% 27.94/3.98  --bmc1_deadlock                         false
% 27.94/3.98  --bmc1_ucm                              false
% 27.94/3.98  --bmc1_add_unsat_core                   none
% 27.94/3.98  --bmc1_unsat_core_children              false
% 27.94/3.98  --bmc1_unsat_core_extrapolate_axioms    false
% 27.94/3.98  --bmc1_out_stat                         full
% 27.94/3.98  --bmc1_ground_init                      false
% 27.94/3.98  --bmc1_pre_inst_next_state              false
% 27.94/3.98  --bmc1_pre_inst_state                   false
% 27.94/3.98  --bmc1_pre_inst_reach_state             false
% 27.94/3.98  --bmc1_out_unsat_core                   false
% 27.94/3.98  --bmc1_aig_witness_out                  false
% 27.94/3.98  --bmc1_verbose                          false
% 27.94/3.98  --bmc1_dump_clauses_tptp                false
% 27.94/3.98  --bmc1_dump_unsat_core_tptp             false
% 27.94/3.98  --bmc1_dump_file                        -
% 27.94/3.98  --bmc1_ucm_expand_uc_limit              128
% 27.94/3.98  --bmc1_ucm_n_expand_iterations          6
% 27.94/3.98  --bmc1_ucm_extend_mode                  1
% 27.94/3.98  --bmc1_ucm_init_mode                    2
% 27.94/3.98  --bmc1_ucm_cone_mode                    none
% 27.94/3.98  --bmc1_ucm_reduced_relation_type        0
% 27.94/3.98  --bmc1_ucm_relax_model                  4
% 27.94/3.98  --bmc1_ucm_full_tr_after_sat            true
% 27.94/3.98  --bmc1_ucm_expand_neg_assumptions       false
% 27.94/3.98  --bmc1_ucm_layered_model                none
% 27.94/3.98  --bmc1_ucm_max_lemma_size               10
% 27.94/3.98  
% 27.94/3.98  ------ AIG Options
% 27.94/3.98  
% 27.94/3.98  --aig_mode                              false
% 27.94/3.98  
% 27.94/3.98  ------ Instantiation Options
% 27.94/3.98  
% 27.94/3.98  --instantiation_flag                    true
% 27.94/3.98  --inst_sos_flag                         true
% 27.94/3.98  --inst_sos_phase                        true
% 27.94/3.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.94/3.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.94/3.98  --inst_lit_sel_side                     num_symb
% 27.94/3.98  --inst_solver_per_active                1400
% 27.94/3.98  --inst_solver_calls_frac                1.
% 27.94/3.98  --inst_passive_queue_type               priority_queues
% 27.94/3.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.94/3.98  --inst_passive_queues_freq              [25;2]
% 27.94/3.98  --inst_dismatching                      true
% 27.94/3.98  --inst_eager_unprocessed_to_passive     true
% 27.94/3.98  --inst_prop_sim_given                   true
% 27.94/3.98  --inst_prop_sim_new                     false
% 27.94/3.98  --inst_subs_new                         false
% 27.94/3.98  --inst_eq_res_simp                      false
% 27.94/3.98  --inst_subs_given                       false
% 27.94/3.98  --inst_orphan_elimination               true
% 27.94/3.98  --inst_learning_loop_flag               true
% 27.94/3.98  --inst_learning_start                   3000
% 27.94/3.98  --inst_learning_factor                  2
% 27.94/3.98  --inst_start_prop_sim_after_learn       3
% 27.94/3.98  --inst_sel_renew                        solver
% 27.94/3.98  --inst_lit_activity_flag                true
% 27.94/3.98  --inst_restr_to_given                   false
% 27.94/3.98  --inst_activity_threshold               500
% 27.94/3.98  --inst_out_proof                        true
% 27.94/3.98  
% 27.94/3.98  ------ Resolution Options
% 27.94/3.98  
% 27.94/3.98  --resolution_flag                       true
% 27.94/3.98  --res_lit_sel                           adaptive
% 27.94/3.98  --res_lit_sel_side                      none
% 27.94/3.98  --res_ordering                          kbo
% 27.94/3.98  --res_to_prop_solver                    active
% 27.94/3.98  --res_prop_simpl_new                    false
% 27.94/3.98  --res_prop_simpl_given                  true
% 27.94/3.98  --res_passive_queue_type                priority_queues
% 27.94/3.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.94/3.98  --res_passive_queues_freq               [15;5]
% 27.94/3.98  --res_forward_subs                      full
% 27.94/3.98  --res_backward_subs                     full
% 27.94/3.98  --res_forward_subs_resolution           true
% 27.94/3.98  --res_backward_subs_resolution          true
% 27.94/3.98  --res_orphan_elimination                true
% 27.94/3.98  --res_time_limit                        2.
% 27.94/3.98  --res_out_proof                         true
% 27.94/3.98  
% 27.94/3.98  ------ Superposition Options
% 27.94/3.98  
% 27.94/3.98  --superposition_flag                    true
% 27.94/3.98  --sup_passive_queue_type                priority_queues
% 27.94/3.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.94/3.98  --sup_passive_queues_freq               [8;1;4]
% 27.94/3.98  --demod_completeness_check              fast
% 27.94/3.98  --demod_use_ground                      true
% 27.94/3.98  --sup_to_prop_solver                    passive
% 27.94/3.98  --sup_prop_simpl_new                    true
% 27.94/3.98  --sup_prop_simpl_given                  true
% 27.94/3.98  --sup_fun_splitting                     true
% 27.94/3.98  --sup_smt_interval                      50000
% 27.94/3.98  
% 27.94/3.98  ------ Superposition Simplification Setup
% 27.94/3.98  
% 27.94/3.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 27.94/3.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 27.94/3.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 27.94/3.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 27.94/3.98  --sup_full_triv                         [TrivRules;PropSubs]
% 27.94/3.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 27.94/3.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 27.94/3.98  --sup_immed_triv                        [TrivRules]
% 27.94/3.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.94/3.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.94/3.98  --sup_immed_bw_main                     []
% 27.94/3.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 27.94/3.98  --sup_input_triv                        [Unflattening;TrivRules]
% 27.94/3.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.94/3.98  --sup_input_bw                          []
% 27.94/3.98  
% 27.94/3.98  ------ Combination Options
% 27.94/3.98  
% 27.94/3.98  --comb_res_mult                         3
% 27.94/3.98  --comb_sup_mult                         2
% 27.94/3.98  --comb_inst_mult                        10
% 27.94/3.98  
% 27.94/3.98  ------ Debug Options
% 27.94/3.98  
% 27.94/3.98  --dbg_backtrace                         false
% 27.94/3.98  --dbg_dump_prop_clauses                 false
% 27.94/3.98  --dbg_dump_prop_clauses_file            -
% 27.94/3.98  --dbg_out_stat                          false
% 27.94/3.98  ------ Parsing...
% 27.94/3.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.94/3.98  
% 27.94/3.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 27.94/3.98  
% 27.94/3.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.94/3.98  
% 27.94/3.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.94/3.98  ------ Proving...
% 27.94/3.98  ------ Problem Properties 
% 27.94/3.98  
% 27.94/3.98  
% 27.94/3.98  clauses                                 32
% 27.94/3.98  conjectures                             3
% 27.94/3.98  EPR                                     5
% 27.94/3.98  Horn                                    30
% 27.94/3.98  unary                                   11
% 27.94/3.98  binary                                  12
% 27.94/3.98  lits                                    62
% 27.94/3.98  lits eq                                 18
% 27.94/3.98  fd_pure                                 0
% 27.94/3.98  fd_pseudo                               0
% 27.94/3.98  fd_cond                                 1
% 27.94/3.98  fd_pseudo_cond                          1
% 27.94/3.98  AC symbols                              0
% 27.94/3.98  
% 27.94/3.98  ------ Schedule dynamic 5 is on 
% 27.94/3.98  
% 27.94/3.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 27.94/3.98  
% 27.94/3.98  
% 27.94/3.98  ------ 
% 27.94/3.98  Current options:
% 27.94/3.98  ------ 
% 27.94/3.98  
% 27.94/3.98  ------ Input Options
% 27.94/3.98  
% 27.94/3.98  --out_options                           all
% 27.94/3.98  --tptp_safe_out                         true
% 27.94/3.98  --problem_path                          ""
% 27.94/3.98  --include_path                          ""
% 27.94/3.98  --clausifier                            res/vclausify_rel
% 27.94/3.98  --clausifier_options                    ""
% 27.94/3.98  --stdin                                 false
% 27.94/3.98  --stats_out                             all
% 27.94/3.98  
% 27.94/3.98  ------ General Options
% 27.94/3.98  
% 27.94/3.98  --fof                                   false
% 27.94/3.98  --time_out_real                         305.
% 27.94/3.98  --time_out_virtual                      -1.
% 27.94/3.98  --symbol_type_check                     false
% 27.94/3.98  --clausify_out                          false
% 27.94/3.98  --sig_cnt_out                           false
% 27.94/3.98  --trig_cnt_out                          false
% 27.94/3.98  --trig_cnt_out_tolerance                1.
% 27.94/3.98  --trig_cnt_out_sk_spl                   false
% 27.94/3.98  --abstr_cl_out                          false
% 27.94/3.98  
% 27.94/3.98  ------ Global Options
% 27.94/3.98  
% 27.94/3.98  --schedule                              default
% 27.94/3.98  --add_important_lit                     false
% 27.94/3.98  --prop_solver_per_cl                    1000
% 27.94/3.98  --min_unsat_core                        false
% 27.94/3.98  --soft_assumptions                      false
% 27.94/3.98  --soft_lemma_size                       3
% 27.94/3.98  --prop_impl_unit_size                   0
% 27.94/3.98  --prop_impl_unit                        []
% 27.94/3.98  --share_sel_clauses                     true
% 27.94/3.98  --reset_solvers                         false
% 27.94/3.98  --bc_imp_inh                            [conj_cone]
% 27.94/3.98  --conj_cone_tolerance                   3.
% 27.94/3.98  --extra_neg_conj                        none
% 27.94/3.98  --large_theory_mode                     true
% 27.94/3.98  --prolific_symb_bound                   200
% 27.94/3.98  --lt_threshold                          2000
% 27.94/3.98  --clause_weak_htbl                      true
% 27.94/3.98  --gc_record_bc_elim                     false
% 27.94/3.98  
% 27.94/3.98  ------ Preprocessing Options
% 27.94/3.98  
% 27.94/3.98  --preprocessing_flag                    true
% 27.94/3.98  --time_out_prep_mult                    0.1
% 27.94/3.98  --splitting_mode                        input
% 27.94/3.98  --splitting_grd                         true
% 27.94/3.98  --splitting_cvd                         false
% 27.94/3.98  --splitting_cvd_svl                     false
% 27.94/3.98  --splitting_nvd                         32
% 27.94/3.98  --sub_typing                            true
% 27.94/3.98  --prep_gs_sim                           true
% 27.94/3.98  --prep_unflatten                        true
% 27.94/3.98  --prep_res_sim                          true
% 27.94/3.98  --prep_upred                            true
% 27.94/3.98  --prep_sem_filter                       exhaustive
% 27.94/3.98  --prep_sem_filter_out                   false
% 27.94/3.98  --pred_elim                             true
% 27.94/3.98  --res_sim_input                         true
% 27.94/3.98  --eq_ax_congr_red                       true
% 27.94/3.98  --pure_diseq_elim                       true
% 27.94/3.98  --brand_transform                       false
% 27.94/3.98  --non_eq_to_eq                          false
% 27.94/3.98  --prep_def_merge                        true
% 27.94/3.98  --prep_def_merge_prop_impl              false
% 27.94/3.98  --prep_def_merge_mbd                    true
% 27.94/3.98  --prep_def_merge_tr_red                 false
% 27.94/3.98  --prep_def_merge_tr_cl                  false
% 27.94/3.98  --smt_preprocessing                     true
% 27.94/3.98  --smt_ac_axioms                         fast
% 27.94/3.98  --preprocessed_out                      false
% 27.94/3.98  --preprocessed_stats                    false
% 27.94/3.98  
% 27.94/3.98  ------ Abstraction refinement Options
% 27.94/3.98  
% 27.94/3.98  --abstr_ref                             []
% 27.94/3.98  --abstr_ref_prep                        false
% 27.94/3.98  --abstr_ref_until_sat                   false
% 27.94/3.98  --abstr_ref_sig_restrict                funpre
% 27.94/3.98  --abstr_ref_af_restrict_to_split_sk     false
% 27.94/3.98  --abstr_ref_under                       []
% 27.94/3.98  
% 27.94/3.98  ------ SAT Options
% 27.94/3.98  
% 27.94/3.98  --sat_mode                              false
% 27.94/3.98  --sat_fm_restart_options                ""
% 27.94/3.98  --sat_gr_def                            false
% 27.94/3.98  --sat_epr_types                         true
% 27.94/3.98  --sat_non_cyclic_types                  false
% 27.94/3.98  --sat_finite_models                     false
% 27.94/3.98  --sat_fm_lemmas                         false
% 27.94/3.98  --sat_fm_prep                           false
% 27.94/3.98  --sat_fm_uc_incr                        true
% 27.94/3.98  --sat_out_model                         small
% 27.94/3.98  --sat_out_clauses                       false
% 27.94/3.98  
% 27.94/3.98  ------ QBF Options
% 27.94/3.98  
% 27.94/3.98  --qbf_mode                              false
% 27.94/3.98  --qbf_elim_univ                         false
% 27.94/3.98  --qbf_dom_inst                          none
% 27.94/3.98  --qbf_dom_pre_inst                      false
% 27.94/3.98  --qbf_sk_in                             false
% 27.94/3.98  --qbf_pred_elim                         true
% 27.94/3.98  --qbf_split                             512
% 27.94/3.98  
% 27.94/3.98  ------ BMC1 Options
% 27.94/3.98  
% 27.94/3.98  --bmc1_incremental                      false
% 27.94/3.98  --bmc1_axioms                           reachable_all
% 27.94/3.98  --bmc1_min_bound                        0
% 27.94/3.98  --bmc1_max_bound                        -1
% 27.94/3.98  --bmc1_max_bound_default                -1
% 27.94/3.98  --bmc1_symbol_reachability              true
% 27.94/3.98  --bmc1_property_lemmas                  false
% 27.94/3.98  --bmc1_k_induction                      false
% 27.94/3.98  --bmc1_non_equiv_states                 false
% 27.94/3.98  --bmc1_deadlock                         false
% 27.94/3.98  --bmc1_ucm                              false
% 27.94/3.98  --bmc1_add_unsat_core                   none
% 27.94/3.98  --bmc1_unsat_core_children              false
% 27.94/3.98  --bmc1_unsat_core_extrapolate_axioms    false
% 27.94/3.98  --bmc1_out_stat                         full
% 27.94/3.98  --bmc1_ground_init                      false
% 27.94/3.98  --bmc1_pre_inst_next_state              false
% 27.94/3.98  --bmc1_pre_inst_state                   false
% 27.94/3.98  --bmc1_pre_inst_reach_state             false
% 27.94/3.98  --bmc1_out_unsat_core                   false
% 27.94/3.98  --bmc1_aig_witness_out                  false
% 27.94/3.98  --bmc1_verbose                          false
% 27.94/3.98  --bmc1_dump_clauses_tptp                false
% 27.94/3.98  --bmc1_dump_unsat_core_tptp             false
% 27.94/3.98  --bmc1_dump_file                        -
% 27.94/3.98  --bmc1_ucm_expand_uc_limit              128
% 27.94/3.98  --bmc1_ucm_n_expand_iterations          6
% 27.94/3.98  --bmc1_ucm_extend_mode                  1
% 27.94/3.98  --bmc1_ucm_init_mode                    2
% 27.94/3.98  --bmc1_ucm_cone_mode                    none
% 27.94/3.98  --bmc1_ucm_reduced_relation_type        0
% 27.94/3.98  --bmc1_ucm_relax_model                  4
% 27.94/3.98  --bmc1_ucm_full_tr_after_sat            true
% 27.94/3.98  --bmc1_ucm_expand_neg_assumptions       false
% 27.94/3.98  --bmc1_ucm_layered_model                none
% 27.94/3.98  --bmc1_ucm_max_lemma_size               10
% 27.94/3.98  
% 27.94/3.98  ------ AIG Options
% 27.94/3.98  
% 27.94/3.98  --aig_mode                              false
% 27.94/3.98  
% 27.94/3.98  ------ Instantiation Options
% 27.94/3.98  
% 27.94/3.98  --instantiation_flag                    true
% 27.94/3.98  --inst_sos_flag                         true
% 27.94/3.98  --inst_sos_phase                        true
% 27.94/3.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.94/3.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.94/3.98  --inst_lit_sel_side                     none
% 27.94/3.98  --inst_solver_per_active                1400
% 27.94/3.98  --inst_solver_calls_frac                1.
% 27.94/3.98  --inst_passive_queue_type               priority_queues
% 27.94/3.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.94/3.98  --inst_passive_queues_freq              [25;2]
% 27.94/3.98  --inst_dismatching                      true
% 27.94/3.98  --inst_eager_unprocessed_to_passive     true
% 27.94/3.98  --inst_prop_sim_given                   true
% 27.94/3.98  --inst_prop_sim_new                     false
% 27.94/3.98  --inst_subs_new                         false
% 27.94/3.98  --inst_eq_res_simp                      false
% 27.94/3.98  --inst_subs_given                       false
% 27.94/3.98  --inst_orphan_elimination               true
% 27.94/3.98  --inst_learning_loop_flag               true
% 27.94/3.98  --inst_learning_start                   3000
% 27.94/3.98  --inst_learning_factor                  2
% 27.94/3.98  --inst_start_prop_sim_after_learn       3
% 27.94/3.98  --inst_sel_renew                        solver
% 27.94/3.98  --inst_lit_activity_flag                true
% 27.94/3.98  --inst_restr_to_given                   false
% 27.94/3.98  --inst_activity_threshold               500
% 27.94/3.98  --inst_out_proof                        true
% 27.94/3.98  
% 27.94/3.98  ------ Resolution Options
% 27.94/3.98  
% 27.94/3.98  --resolution_flag                       false
% 27.94/3.98  --res_lit_sel                           adaptive
% 27.94/3.98  --res_lit_sel_side                      none
% 27.94/3.98  --res_ordering                          kbo
% 27.94/3.98  --res_to_prop_solver                    active
% 27.94/3.98  --res_prop_simpl_new                    false
% 27.94/3.98  --res_prop_simpl_given                  true
% 27.94/3.98  --res_passive_queue_type                priority_queues
% 27.94/3.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.94/3.98  --res_passive_queues_freq               [15;5]
% 27.94/3.98  --res_forward_subs                      full
% 27.94/3.98  --res_backward_subs                     full
% 27.94/3.98  --res_forward_subs_resolution           true
% 27.94/3.98  --res_backward_subs_resolution          true
% 27.94/3.98  --res_orphan_elimination                true
% 27.94/3.98  --res_time_limit                        2.
% 27.94/3.98  --res_out_proof                         true
% 27.94/3.98  
% 27.94/3.98  ------ Superposition Options
% 27.94/3.98  
% 27.94/3.98  --superposition_flag                    true
% 27.94/3.98  --sup_passive_queue_type                priority_queues
% 27.94/3.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.94/3.98  --sup_passive_queues_freq               [8;1;4]
% 27.94/3.98  --demod_completeness_check              fast
% 27.94/3.98  --demod_use_ground                      true
% 27.94/3.98  --sup_to_prop_solver                    passive
% 27.94/3.98  --sup_prop_simpl_new                    true
% 27.94/3.98  --sup_prop_simpl_given                  true
% 27.94/3.98  --sup_fun_splitting                     true
% 27.94/3.98  --sup_smt_interval                      50000
% 27.94/3.98  
% 27.94/3.98  ------ Superposition Simplification Setup
% 27.94/3.98  
% 27.94/3.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 27.94/3.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 27.94/3.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 27.94/3.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 27.94/3.98  --sup_full_triv                         [TrivRules;PropSubs]
% 27.94/3.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 27.94/3.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 27.94/3.98  --sup_immed_triv                        [TrivRules]
% 27.94/3.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.94/3.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.94/3.98  --sup_immed_bw_main                     []
% 27.94/3.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 27.94/3.98  --sup_input_triv                        [Unflattening;TrivRules]
% 27.94/3.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.94/3.98  --sup_input_bw                          []
% 27.94/3.98  
% 27.94/3.98  ------ Combination Options
% 27.94/3.98  
% 27.94/3.98  --comb_res_mult                         3
% 27.94/3.98  --comb_sup_mult                         2
% 27.94/3.98  --comb_inst_mult                        10
% 27.94/3.98  
% 27.94/3.98  ------ Debug Options
% 27.94/3.98  
% 27.94/3.98  --dbg_backtrace                         false
% 27.94/3.98  --dbg_dump_prop_clauses                 false
% 27.94/3.98  --dbg_dump_prop_clauses_file            -
% 27.94/3.98  --dbg_out_stat                          false
% 27.94/3.98  
% 27.94/3.98  
% 27.94/3.98  
% 27.94/3.98  
% 27.94/3.98  ------ Proving...
% 27.94/3.98  
% 27.94/3.98  
% 27.94/3.98  % SZS status Theorem for theBenchmark.p
% 27.94/3.98  
% 27.94/3.98   Resolution empty clause
% 27.94/3.98  
% 27.94/3.98  % SZS output start CNFRefutation for theBenchmark.p
% 27.94/3.98  
% 27.94/3.98  fof(f4,axiom,(
% 27.94/3.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 27.94/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.94/3.98  
% 27.94/3.98  fof(f64,plain,(
% 27.94/3.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 27.94/3.98    inference(cnf_transformation,[],[f4])).
% 27.94/3.98  
% 27.94/3.98  fof(f19,axiom,(
% 27.94/3.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 27.94/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.94/3.98  
% 27.94/3.98  fof(f85,plain,(
% 27.94/3.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 27.94/3.98    inference(cnf_transformation,[],[f19])).
% 27.94/3.98  
% 27.94/3.98  fof(f29,conjecture,(
% 27.94/3.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 27.94/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.94/3.98  
% 27.94/3.98  fof(f30,negated_conjecture,(
% 27.94/3.98    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 27.94/3.98    inference(negated_conjecture,[],[f29])).
% 27.94/3.98  
% 27.94/3.98  fof(f31,plain,(
% 27.94/3.98    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 27.94/3.98    inference(pure_predicate_removal,[],[f30])).
% 27.94/3.98  
% 27.94/3.98  fof(f47,plain,(
% 27.94/3.98    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 27.94/3.98    inference(ennf_transformation,[],[f31])).
% 27.94/3.98  
% 27.94/3.98  fof(f48,plain,(
% 27.94/3.98    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 27.94/3.98    inference(flattening,[],[f47])).
% 27.94/3.98  
% 27.94/3.98  fof(f57,plain,(
% 27.94/3.98    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3))),
% 27.94/3.98    introduced(choice_axiom,[])).
% 27.94/3.98  
% 27.94/3.98  fof(f58,plain,(
% 27.94/3.98    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3)),
% 27.94/3.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f48,f57])).
% 27.94/3.98  
% 27.94/3.98  fof(f98,plain,(
% 27.94/3.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 27.94/3.98    inference(cnf_transformation,[],[f58])).
% 27.94/3.98  
% 27.94/3.98  fof(f6,axiom,(
% 27.94/3.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 27.94/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.94/3.98  
% 27.94/3.98  fof(f66,plain,(
% 27.94/3.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 27.94/3.98    inference(cnf_transformation,[],[f6])).
% 27.94/3.98  
% 27.94/3.98  fof(f7,axiom,(
% 27.94/3.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 27.94/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.94/3.98  
% 27.94/3.98  fof(f67,plain,(
% 27.94/3.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 27.94/3.98    inference(cnf_transformation,[],[f7])).
% 27.94/3.98  
% 27.94/3.98  fof(f8,axiom,(
% 27.94/3.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 27.94/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.94/3.98  
% 27.94/3.98  fof(f68,plain,(
% 27.94/3.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 27.94/3.98    inference(cnf_transformation,[],[f8])).
% 27.94/3.98  
% 27.94/3.98  fof(f9,axiom,(
% 27.94/3.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 27.94/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.94/3.98  
% 27.94/3.98  fof(f69,plain,(
% 27.94/3.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 27.94/3.98    inference(cnf_transformation,[],[f9])).
% 27.94/3.98  
% 27.94/3.98  fof(f10,axiom,(
% 27.94/3.98    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 27.94/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.94/3.98  
% 27.94/3.98  fof(f70,plain,(
% 27.94/3.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 27.94/3.98    inference(cnf_transformation,[],[f10])).
% 27.94/3.98  
% 27.94/3.98  fof(f11,axiom,(
% 27.94/3.98    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 27.94/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.94/3.98  
% 27.94/3.98  fof(f71,plain,(
% 27.94/3.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 27.94/3.98    inference(cnf_transformation,[],[f11])).
% 27.94/3.98  
% 27.94/3.98  fof(f12,axiom,(
% 27.94/3.98    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 27.94/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.94/3.98  
% 27.94/3.98  fof(f72,plain,(
% 27.94/3.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 27.94/3.98    inference(cnf_transformation,[],[f12])).
% 27.94/3.98  
% 27.94/3.98  fof(f101,plain,(
% 27.94/3.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 27.94/3.98    inference(definition_unfolding,[],[f71,f72])).
% 27.94/3.98  
% 27.94/3.98  fof(f102,plain,(
% 27.94/3.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 27.94/3.98    inference(definition_unfolding,[],[f70,f101])).
% 27.94/3.98  
% 27.94/3.98  fof(f103,plain,(
% 27.94/3.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 27.94/3.98    inference(definition_unfolding,[],[f69,f102])).
% 27.94/3.98  
% 27.94/3.98  fof(f104,plain,(
% 27.94/3.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 27.94/3.98    inference(definition_unfolding,[],[f68,f103])).
% 27.94/3.98  
% 27.94/3.98  fof(f105,plain,(
% 27.94/3.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 27.94/3.98    inference(definition_unfolding,[],[f67,f104])).
% 27.94/3.98  
% 27.94/3.98  fof(f106,plain,(
% 27.94/3.98    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 27.94/3.98    inference(definition_unfolding,[],[f66,f105])).
% 27.94/3.98  
% 27.94/3.98  fof(f113,plain,(
% 27.94/3.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))),
% 27.94/3.98    inference(definition_unfolding,[],[f98,f106])).
% 27.94/3.98  
% 27.94/3.98  fof(f16,axiom,(
% 27.94/3.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 27.94/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.94/3.98  
% 27.94/3.98  fof(f55,plain,(
% 27.94/3.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 27.94/3.98    inference(nnf_transformation,[],[f16])).
% 27.94/3.98  
% 27.94/3.98  fof(f80,plain,(
% 27.94/3.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 27.94/3.98    inference(cnf_transformation,[],[f55])).
% 27.94/3.98  
% 27.94/3.98  fof(f17,axiom,(
% 27.94/3.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 27.94/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.94/3.98  
% 27.94/3.98  fof(f34,plain,(
% 27.94/3.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 27.94/3.98    inference(ennf_transformation,[],[f17])).
% 27.94/3.98  
% 27.94/3.98  fof(f82,plain,(
% 27.94/3.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 27.94/3.98    inference(cnf_transformation,[],[f34])).
% 27.94/3.98  
% 27.94/3.98  fof(f81,plain,(
% 27.94/3.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 27.94/3.98    inference(cnf_transformation,[],[f55])).
% 27.94/3.98  
% 27.94/3.98  fof(f1,axiom,(
% 27.94/3.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 27.94/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.94/3.98  
% 27.94/3.98  fof(f49,plain,(
% 27.94/3.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 27.94/3.98    inference(nnf_transformation,[],[f1])).
% 27.94/3.98  
% 27.94/3.98  fof(f50,plain,(
% 27.94/3.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 27.94/3.99    inference(flattening,[],[f49])).
% 27.94/3.99  
% 27.94/3.99  fof(f60,plain,(
% 27.94/3.99    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 27.94/3.99    inference(cnf_transformation,[],[f50])).
% 27.94/3.99  
% 27.94/3.99  fof(f114,plain,(
% 27.94/3.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 27.94/3.99    inference(equality_resolution,[],[f60])).
% 27.94/3.99  
% 27.94/3.99  fof(f18,axiom,(
% 27.94/3.99    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 27.94/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.94/3.99  
% 27.94/3.99  fof(f35,plain,(
% 27.94/3.99    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 27.94/3.99    inference(ennf_transformation,[],[f18])).
% 27.94/3.99  
% 27.94/3.99  fof(f56,plain,(
% 27.94/3.99    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 27.94/3.99    inference(nnf_transformation,[],[f35])).
% 27.94/3.99  
% 27.94/3.99  fof(f84,plain,(
% 27.94/3.99    ( ! [X0,X1] : (v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 27.94/3.99    inference(cnf_transformation,[],[f56])).
% 27.94/3.99  
% 27.94/3.99  fof(f21,axiom,(
% 27.94/3.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 27.94/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.94/3.99  
% 27.94/3.99  fof(f37,plain,(
% 27.94/3.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 27.94/3.99    inference(ennf_transformation,[],[f21])).
% 27.94/3.99  
% 27.94/3.99  fof(f38,plain,(
% 27.94/3.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 27.94/3.99    inference(flattening,[],[f37])).
% 27.94/3.99  
% 27.94/3.99  fof(f87,plain,(
% 27.94/3.99    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 27.94/3.99    inference(cnf_transformation,[],[f38])).
% 27.94/3.99  
% 27.94/3.99  fof(f20,axiom,(
% 27.94/3.99    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 27.94/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.94/3.99  
% 27.94/3.99  fof(f36,plain,(
% 27.94/3.99    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 27.94/3.99    inference(ennf_transformation,[],[f20])).
% 27.94/3.99  
% 27.94/3.99  fof(f86,plain,(
% 27.94/3.99    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 27.94/3.99    inference(cnf_transformation,[],[f36])).
% 27.94/3.99  
% 27.94/3.99  fof(f25,axiom,(
% 27.94/3.99    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 27.94/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.94/3.99  
% 27.94/3.99  fof(f42,plain,(
% 27.94/3.99    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 27.94/3.99    inference(ennf_transformation,[],[f25])).
% 27.94/3.99  
% 27.94/3.99  fof(f93,plain,(
% 27.94/3.99    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 27.94/3.99    inference(cnf_transformation,[],[f42])).
% 27.94/3.99  
% 27.94/3.99  fof(f23,axiom,(
% 27.94/3.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 27.94/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.94/3.99  
% 27.94/3.99  fof(f40,plain,(
% 27.94/3.99    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 27.94/3.99    inference(ennf_transformation,[],[f23])).
% 27.94/3.99  
% 27.94/3.99  fof(f41,plain,(
% 27.94/3.99    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 27.94/3.99    inference(flattening,[],[f40])).
% 27.94/3.99  
% 27.94/3.99  fof(f90,plain,(
% 27.94/3.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 27.94/3.99    inference(cnf_transformation,[],[f41])).
% 27.94/3.99  
% 27.94/3.99  fof(f15,axiom,(
% 27.94/3.99    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 27.94/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.94/3.99  
% 27.94/3.99  fof(f54,plain,(
% 27.94/3.99    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 27.94/3.99    inference(nnf_transformation,[],[f15])).
% 27.94/3.99  
% 27.94/3.99  fof(f79,plain,(
% 27.94/3.99    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 27.94/3.99    inference(cnf_transformation,[],[f54])).
% 27.94/3.99  
% 27.94/3.99  fof(f2,axiom,(
% 27.94/3.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 27.94/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.94/3.99  
% 27.94/3.99  fof(f62,plain,(
% 27.94/3.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 27.94/3.99    inference(cnf_transformation,[],[f2])).
% 27.94/3.99  
% 27.94/3.99  fof(f109,plain,(
% 27.94/3.99    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = X0 | r2_hidden(X1,X0)) )),
% 27.94/3.99    inference(definition_unfolding,[],[f79,f62,f106])).
% 27.94/3.99  
% 27.94/3.99  fof(f27,axiom,(
% 27.94/3.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 27.94/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.94/3.99  
% 27.94/3.99  fof(f32,plain,(
% 27.94/3.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 27.94/3.99    inference(pure_predicate_removal,[],[f27])).
% 27.94/3.99  
% 27.94/3.99  fof(f45,plain,(
% 27.94/3.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.94/3.99    inference(ennf_transformation,[],[f32])).
% 27.94/3.99  
% 27.94/3.99  fof(f95,plain,(
% 27.94/3.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 27.94/3.99    inference(cnf_transformation,[],[f45])).
% 27.94/3.99  
% 27.94/3.99  fof(f13,axiom,(
% 27.94/3.99    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 27.94/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.94/3.99  
% 27.94/3.99  fof(f51,plain,(
% 27.94/3.99    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 27.94/3.99    inference(nnf_transformation,[],[f13])).
% 27.94/3.99  
% 27.94/3.99  fof(f74,plain,(
% 27.94/3.99    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 27.94/3.99    inference(cnf_transformation,[],[f51])).
% 27.94/3.99  
% 27.94/3.99  fof(f107,plain,(
% 27.94/3.99    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 27.94/3.99    inference(definition_unfolding,[],[f74,f106])).
% 27.94/3.99  
% 27.94/3.99  fof(f83,plain,(
% 27.94/3.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 27.94/3.99    inference(cnf_transformation,[],[f56])).
% 27.94/3.99  
% 27.94/3.99  fof(f61,plain,(
% 27.94/3.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 27.94/3.99    inference(cnf_transformation,[],[f50])).
% 27.94/3.99  
% 27.94/3.99  fof(f3,axiom,(
% 27.94/3.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 27.94/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.94/3.99  
% 27.94/3.99  fof(f33,plain,(
% 27.94/3.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 27.94/3.99    inference(ennf_transformation,[],[f3])).
% 27.94/3.99  
% 27.94/3.99  fof(f63,plain,(
% 27.94/3.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 27.94/3.99    inference(cnf_transformation,[],[f33])).
% 27.94/3.99  
% 27.94/3.99  fof(f5,axiom,(
% 27.94/3.99    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 27.94/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.94/3.99  
% 27.94/3.99  fof(f65,plain,(
% 27.94/3.99    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 27.94/3.99    inference(cnf_transformation,[],[f5])).
% 27.94/3.99  
% 27.94/3.99  fof(f26,axiom,(
% 27.94/3.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 27.94/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.94/3.99  
% 27.94/3.99  fof(f43,plain,(
% 27.94/3.99    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 27.94/3.99    inference(ennf_transformation,[],[f26])).
% 27.94/3.99  
% 27.94/3.99  fof(f44,plain,(
% 27.94/3.99    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 27.94/3.99    inference(flattening,[],[f43])).
% 27.94/3.99  
% 27.94/3.99  fof(f94,plain,(
% 27.94/3.99    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 27.94/3.99    inference(cnf_transformation,[],[f44])).
% 27.94/3.99  
% 27.94/3.99  fof(f111,plain,(
% 27.94/3.99    ( ! [X0,X1] : (k6_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 27.94/3.99    inference(definition_unfolding,[],[f94,f106,f106])).
% 27.94/3.99  
% 27.94/3.99  fof(f97,plain,(
% 27.94/3.99    v1_funct_1(sK3)),
% 27.94/3.99    inference(cnf_transformation,[],[f58])).
% 27.94/3.99  
% 27.94/3.99  fof(f28,axiom,(
% 27.94/3.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 27.94/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.94/3.99  
% 27.94/3.99  fof(f46,plain,(
% 27.94/3.99    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.94/3.99    inference(ennf_transformation,[],[f28])).
% 27.94/3.99  
% 27.94/3.99  fof(f96,plain,(
% 27.94/3.99    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 27.94/3.99    inference(cnf_transformation,[],[f46])).
% 27.94/3.99  
% 27.94/3.99  fof(f100,plain,(
% 27.94/3.99    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 27.94/3.99    inference(cnf_transformation,[],[f58])).
% 27.94/3.99  
% 27.94/3.99  fof(f112,plain,(
% 27.94/3.99    ~r1_tarski(k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 27.94/3.99    inference(definition_unfolding,[],[f100,f106,f106])).
% 27.94/3.99  
% 27.94/3.99  fof(f22,axiom,(
% 27.94/3.99    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 27.94/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.94/3.99  
% 27.94/3.99  fof(f39,plain,(
% 27.94/3.99    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 27.94/3.99    inference(ennf_transformation,[],[f22])).
% 27.94/3.99  
% 27.94/3.99  fof(f88,plain,(
% 27.94/3.99    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 27.94/3.99    inference(cnf_transformation,[],[f39])).
% 27.94/3.99  
% 27.94/3.99  fof(f14,axiom,(
% 27.94/3.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 27.94/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.94/3.99  
% 27.94/3.99  fof(f52,plain,(
% 27.94/3.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 27.94/3.99    inference(nnf_transformation,[],[f14])).
% 27.94/3.99  
% 27.94/3.99  fof(f53,plain,(
% 27.94/3.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 27.94/3.99    inference(flattening,[],[f52])).
% 27.94/3.99  
% 27.94/3.99  fof(f76,plain,(
% 27.94/3.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 27.94/3.99    inference(cnf_transformation,[],[f53])).
% 27.94/3.99  
% 27.94/3.99  fof(f117,plain,(
% 27.94/3.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 27.94/3.99    inference(equality_resolution,[],[f76])).
% 27.94/3.99  
% 27.94/3.99  fof(f24,axiom,(
% 27.94/3.99    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 27.94/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.94/3.99  
% 27.94/3.99  fof(f91,plain,(
% 27.94/3.99    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 27.94/3.99    inference(cnf_transformation,[],[f24])).
% 27.94/3.99  
% 27.94/3.99  fof(f77,plain,(
% 27.94/3.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 27.94/3.99    inference(cnf_transformation,[],[f53])).
% 27.94/3.99  
% 27.94/3.99  fof(f116,plain,(
% 27.94/3.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 27.94/3.99    inference(equality_resolution,[],[f77])).
% 27.94/3.99  
% 27.94/3.99  fof(f92,plain,(
% 27.94/3.99    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 27.94/3.99    inference(cnf_transformation,[],[f24])).
% 27.94/3.99  
% 27.94/3.99  cnf(c_4,plain,
% 27.94/3.99      ( r1_tarski(k1_xboole_0,X0) ),
% 27.94/3.99      inference(cnf_transformation,[],[f64]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_1566,plain,
% 27.94/3.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 27.94/3.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_18,plain,
% 27.94/3.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 27.94/3.99      inference(cnf_transformation,[],[f85]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_1557,plain,
% 27.94/3.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 27.94/3.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_32,negated_conjecture,
% 27.94/3.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) ),
% 27.94/3.99      inference(cnf_transformation,[],[f113]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_1549,plain,
% 27.94/3.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
% 27.94/3.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_14,plain,
% 27.94/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 27.94/3.99      inference(cnf_transformation,[],[f80]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_1560,plain,
% 27.94/3.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 27.94/3.99      | r1_tarski(X0,X1) = iProver_top ),
% 27.94/3.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_2794,plain,
% 27.94/3.99      ( r1_tarski(sK3,k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) = iProver_top ),
% 27.94/3.99      inference(superposition,[status(thm)],[c_1549,c_1560]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_15,plain,
% 27.94/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 27.94/3.99      inference(cnf_transformation,[],[f82]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_13,plain,
% 27.94/3.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 27.94/3.99      inference(cnf_transformation,[],[f81]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_246,plain,
% 27.94/3.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 27.94/3.99      inference(prop_impl,[status(thm)],[c_13]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_247,plain,
% 27.94/3.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 27.94/3.99      inference(renaming,[status(thm)],[c_246]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_300,plain,
% 27.94/3.99      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 27.94/3.99      inference(bin_hyper_res,[status(thm)],[c_15,c_247]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_1546,plain,
% 27.94/3.99      ( r1_tarski(X0,X1) != iProver_top
% 27.94/3.99      | v1_relat_1(X1) != iProver_top
% 27.94/3.99      | v1_relat_1(X0) = iProver_top ),
% 27.94/3.99      inference(predicate_to_equality,[status(thm)],[c_300]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_2880,plain,
% 27.94/3.99      ( v1_relat_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != iProver_top
% 27.94/3.99      | v1_relat_1(sK3) = iProver_top ),
% 27.94/3.99      inference(superposition,[status(thm)],[c_2794,c_1546]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_3026,plain,
% 27.94/3.99      ( v1_relat_1(sK3) = iProver_top ),
% 27.94/3.99      inference(superposition,[status(thm)],[c_1557,c_2880]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_1,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f114]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_1568,plain,
% 27.94/3.99      ( r1_tarski(X0,X0) = iProver_top ),
% 27.94/3.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_16,plain,
% 27.94/3.99      ( v4_relat_1(X0,X1) | ~ r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 27.94/3.99      inference(cnf_transformation,[],[f84]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_1559,plain,
% 27.94/3.99      ( v4_relat_1(X0,X1) = iProver_top
% 27.94/3.99      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 27.94/3.99      | v1_relat_1(X0) != iProver_top ),
% 27.94/3.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_4890,plain,
% 27.94/3.99      ( v4_relat_1(X0,k1_relat_1(X0)) = iProver_top
% 27.94/3.99      | v1_relat_1(X0) != iProver_top ),
% 27.94/3.99      inference(superposition,[status(thm)],[c_1568,c_1559]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_20,plain,
% 27.94/3.99      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 27.94/3.99      inference(cnf_transformation,[],[f87]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_1555,plain,
% 27.94/3.99      ( k7_relat_1(X0,X1) = X0
% 27.94/3.99      | v4_relat_1(X0,X1) != iProver_top
% 27.94/3.99      | v1_relat_1(X0) != iProver_top ),
% 27.94/3.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_9768,plain,
% 27.94/3.99      ( k7_relat_1(X0,k1_relat_1(X0)) = X0 | v1_relat_1(X0) != iProver_top ),
% 27.94/3.99      inference(superposition,[status(thm)],[c_4890,c_1555]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_9774,plain,
% 27.94/3.99      ( k7_relat_1(sK3,k1_relat_1(sK3)) = sK3 ),
% 27.94/3.99      inference(superposition,[status(thm)],[c_3026,c_9768]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_19,plain,
% 27.94/3.99      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 27.94/3.99      inference(cnf_transformation,[],[f86]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_1556,plain,
% 27.94/3.99      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 27.94/3.99      | v1_relat_1(X0) != iProver_top ),
% 27.94/3.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_3109,plain,
% 27.94/3.99      ( k2_relat_1(k7_relat_1(sK3,X0)) = k9_relat_1(sK3,X0) ),
% 27.94/3.99      inference(superposition,[status(thm)],[c_3026,c_1556]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_9926,plain,
% 27.94/3.99      ( k9_relat_1(sK3,k1_relat_1(sK3)) = k2_relat_1(sK3) ),
% 27.94/3.99      inference(superposition,[status(thm)],[c_9774,c_3109]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_26,plain,
% 27.94/3.99      ( r1_tarski(k7_relat_1(X0,X1),X0) | ~ v1_relat_1(X0) ),
% 27.94/3.99      inference(cnf_transformation,[],[f93]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_1553,plain,
% 27.94/3.99      ( r1_tarski(k7_relat_1(X0,X1),X0) = iProver_top
% 27.94/3.99      | v1_relat_1(X0) != iProver_top ),
% 27.94/3.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_2738,plain,
% 27.94/3.99      ( v1_relat_1(X0) != iProver_top
% 27.94/3.99      | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
% 27.94/3.99      inference(superposition,[status(thm)],[c_1553,c_1546]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_8719,plain,
% 27.94/3.99      ( k2_relat_1(k7_relat_1(k7_relat_1(X0,X1),X2)) = k9_relat_1(k7_relat_1(X0,X1),X2)
% 27.94/3.99      | v1_relat_1(X0) != iProver_top ),
% 27.94/3.99      inference(superposition,[status(thm)],[c_2738,c_1556]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_17961,plain,
% 27.94/3.99      ( k2_relat_1(k7_relat_1(k7_relat_1(sK3,X0),X1)) = k9_relat_1(k7_relat_1(sK3,X0),X1) ),
% 27.94/3.99      inference(superposition,[status(thm)],[c_3026,c_8719]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_22,plain,
% 27.94/3.99      ( ~ r1_tarski(X0,X1)
% 27.94/3.99      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 27.94/3.99      | ~ v1_relat_1(X0)
% 27.94/3.99      | ~ v1_relat_1(X1) ),
% 27.94/3.99      inference(cnf_transformation,[],[f90]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_176,plain,
% 27.94/3.99      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 27.94/3.99      | ~ r1_tarski(X0,X1)
% 27.94/3.99      | ~ v1_relat_1(X1) ),
% 27.94/3.99      inference(global_propositional_subsumption,
% 27.94/3.99                [status(thm)],
% 27.94/3.99                [c_22,c_15,c_13]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_177,plain,
% 27.94/3.99      ( ~ r1_tarski(X0,X1)
% 27.94/3.99      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 27.94/3.99      | ~ v1_relat_1(X1) ),
% 27.94/3.99      inference(renaming,[status(thm)],[c_176]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_1547,plain,
% 27.94/3.99      ( r1_tarski(X0,X1) != iProver_top
% 27.94/3.99      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
% 27.94/3.99      | v1_relat_1(X1) != iProver_top ),
% 27.94/3.99      inference(predicate_to_equality,[status(thm)],[c_177]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_3112,plain,
% 27.94/3.99      ( r1_tarski(X0,k7_relat_1(sK3,X1)) != iProver_top
% 27.94/3.99      | r1_tarski(k2_relat_1(X0),k9_relat_1(sK3,X1)) = iProver_top
% 27.94/3.99      | v1_relat_1(k7_relat_1(sK3,X1)) != iProver_top ),
% 27.94/3.99      inference(superposition,[status(thm)],[c_3109,c_1547]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_18247,plain,
% 27.94/3.99      ( r1_tarski(k9_relat_1(k7_relat_1(sK3,X0),X1),k9_relat_1(sK3,X2)) = iProver_top
% 27.94/3.99      | r1_tarski(k7_relat_1(k7_relat_1(sK3,X0),X1),k7_relat_1(sK3,X2)) != iProver_top
% 27.94/3.99      | v1_relat_1(k7_relat_1(sK3,X2)) != iProver_top ),
% 27.94/3.99      inference(superposition,[status(thm)],[c_17961,c_3112]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_19222,plain,
% 27.94/3.99      ( r1_tarski(k9_relat_1(k7_relat_1(sK3,X0),X1),k9_relat_1(sK3,X0)) = iProver_top
% 27.94/3.99      | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
% 27.94/3.99      inference(superposition,[status(thm)],[c_1553,c_18247]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_3911,plain,
% 27.94/3.99      ( ~ r1_tarski(X0,sK3) | v1_relat_1(X0) | ~ v1_relat_1(sK3) ),
% 27.94/3.99      inference(instantiation,[status(thm)],[c_300]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_4157,plain,
% 27.94/3.99      ( ~ r1_tarski(k7_relat_1(sK3,X0),sK3)
% 27.94/3.99      | v1_relat_1(k7_relat_1(sK3,X0))
% 27.94/3.99      | ~ v1_relat_1(sK3) ),
% 27.94/3.99      inference(instantiation,[status(thm)],[c_3911]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_4158,plain,
% 27.94/3.99      ( r1_tarski(k7_relat_1(sK3,X0),sK3) != iProver_top
% 27.94/3.99      | v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top
% 27.94/3.99      | v1_relat_1(sK3) != iProver_top ),
% 27.94/3.99      inference(predicate_to_equality,[status(thm)],[c_4157]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_7422,plain,
% 27.94/3.99      ( r1_tarski(k7_relat_1(sK3,X0),sK3) | ~ v1_relat_1(sK3) ),
% 27.94/3.99      inference(instantiation,[status(thm)],[c_26]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_7423,plain,
% 27.94/3.99      ( r1_tarski(k7_relat_1(sK3,X0),sK3) = iProver_top
% 27.94/3.99      | v1_relat_1(sK3) != iProver_top ),
% 27.94/3.99      inference(predicate_to_equality,[status(thm)],[c_7422]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_21823,plain,
% 27.94/3.99      ( r1_tarski(k9_relat_1(k7_relat_1(sK3,X0),X1),k9_relat_1(sK3,X0)) = iProver_top ),
% 27.94/3.99      inference(global_propositional_subsumption,
% 27.94/3.99                [status(thm)],
% 27.94/3.99                [c_19222,c_3026,c_4158,c_7423]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_21832,plain,
% 27.94/3.99      ( r1_tarski(k9_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)),X0),k2_relat_1(sK3)) = iProver_top ),
% 27.94/3.99      inference(superposition,[status(thm)],[c_9926,c_21823]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_21841,plain,
% 27.94/3.99      ( r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3)) = iProver_top ),
% 27.94/3.99      inference(light_normalisation,[status(thm)],[c_21832,c_9774]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_11,plain,
% 27.94/3.99      ( r2_hidden(X0,X1)
% 27.94/3.99      | k5_xboole_0(X1,k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X1 ),
% 27.94/3.99      inference(cnf_transformation,[],[f109]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_1563,plain,
% 27.94/3.99      ( k5_xboole_0(X0,k3_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = X0
% 27.94/3.99      | r2_hidden(X1,X0) = iProver_top ),
% 27.94/3.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_28,plain,
% 27.94/3.99      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 27.94/3.99      inference(cnf_transformation,[],[f95]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_1552,plain,
% 27.94/3.99      ( v4_relat_1(X0,X1) = iProver_top
% 27.94/3.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 27.94/3.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_3413,plain,
% 27.94/3.99      ( v4_relat_1(sK3,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
% 27.94/3.99      inference(superposition,[status(thm)],[c_1549,c_1552]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_6,plain,
% 27.94/3.99      ( ~ r2_hidden(X0,X1)
% 27.94/3.99      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
% 27.94/3.99      inference(cnf_transformation,[],[f107]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_1565,plain,
% 27.94/3.99      ( r2_hidden(X0,X1) != iProver_top
% 27.94/3.99      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top ),
% 27.94/3.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_17,plain,
% 27.94/3.99      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 27.94/3.99      inference(cnf_transformation,[],[f83]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_1558,plain,
% 27.94/3.99      ( v4_relat_1(X0,X1) != iProver_top
% 27.94/3.99      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 27.94/3.99      | v1_relat_1(X0) != iProver_top ),
% 27.94/3.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_0,plain,
% 27.94/3.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 27.94/3.99      inference(cnf_transformation,[],[f61]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_1569,plain,
% 27.94/3.99      ( X0 = X1
% 27.94/3.99      | r1_tarski(X0,X1) != iProver_top
% 27.94/3.99      | r1_tarski(X1,X0) != iProver_top ),
% 27.94/3.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_4025,plain,
% 27.94/3.99      ( k1_relat_1(X0) = X1
% 27.94/3.99      | v4_relat_1(X0,X1) != iProver_top
% 27.94/3.99      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 27.94/3.99      | v1_relat_1(X0) != iProver_top ),
% 27.94/3.99      inference(superposition,[status(thm)],[c_1558,c_1569]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_20867,plain,
% 27.94/3.99      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_relat_1(X1)
% 27.94/3.99      | v4_relat_1(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top
% 27.94/3.99      | r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 27.94/3.99      | v1_relat_1(X1) != iProver_top ),
% 27.94/3.99      inference(superposition,[status(thm)],[c_1565,c_4025]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_106254,plain,
% 27.94/3.99      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
% 27.94/3.99      | r2_hidden(sK0,k1_relat_1(sK3)) != iProver_top
% 27.94/3.99      | v1_relat_1(sK3) != iProver_top ),
% 27.94/3.99      inference(superposition,[status(thm)],[c_3413,c_20867]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_106532,plain,
% 27.94/3.99      ( r2_hidden(sK0,k1_relat_1(sK3)) != iProver_top
% 27.94/3.99      | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(sK3) ),
% 27.94/3.99      inference(global_propositional_subsumption,
% 27.94/3.99                [status(thm)],
% 27.94/3.99                [c_106254,c_3026]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_106533,plain,
% 27.94/3.99      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
% 27.94/3.99      | r2_hidden(sK0,k1_relat_1(sK3)) != iProver_top ),
% 27.94/3.99      inference(renaming,[status(thm)],[c_106532]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_106536,plain,
% 27.94/3.99      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
% 27.94/3.99      | k5_xboole_0(k1_relat_1(sK3),k3_xboole_0(k1_relat_1(sK3),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k1_relat_1(sK3) ),
% 27.94/3.99      inference(superposition,[status(thm)],[c_1563,c_106533]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_3,plain,
% 27.94/3.99      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 27.94/3.99      inference(cnf_transformation,[],[f63]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_1567,plain,
% 27.94/3.99      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 27.94/3.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_4026,plain,
% 27.94/3.99      ( k3_xboole_0(k1_relat_1(X0),X1) = k1_relat_1(X0)
% 27.94/3.99      | v4_relat_1(X0,X1) != iProver_top
% 27.94/3.99      | v1_relat_1(X0) != iProver_top ),
% 27.94/3.99      inference(superposition,[status(thm)],[c_1558,c_1567]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_22699,plain,
% 27.94/3.99      ( k3_xboole_0(k1_relat_1(sK3),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k1_relat_1(sK3)
% 27.94/3.99      | v1_relat_1(sK3) != iProver_top ),
% 27.94/3.99      inference(superposition,[status(thm)],[c_3413,c_4026]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_23073,plain,
% 27.94/3.99      ( k3_xboole_0(k1_relat_1(sK3),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k1_relat_1(sK3) ),
% 27.94/3.99      inference(global_propositional_subsumption,
% 27.94/3.99                [status(thm)],
% 27.94/3.99                [c_22699,c_3026]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_106537,plain,
% 27.94/3.99      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
% 27.94/3.99      | k5_xboole_0(k1_relat_1(sK3),k1_relat_1(sK3)) = k1_relat_1(sK3) ),
% 27.94/3.99      inference(light_normalisation,[status(thm)],[c_106536,c_23073]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_5,plain,
% 27.94/3.99      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 27.94/3.99      inference(cnf_transformation,[],[f65]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_106538,plain,
% 27.94/3.99      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
% 27.94/3.99      | k1_relat_1(sK3) = k1_xboole_0 ),
% 27.94/3.99      inference(demodulation,[status(thm)],[c_106537,c_5]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_27,plain,
% 27.94/3.99      ( ~ v1_funct_1(X0)
% 27.94/3.99      | ~ v1_relat_1(X0)
% 27.94/3.99      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k1_relat_1(X0)
% 27.94/3.99      | k6_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
% 27.94/3.99      inference(cnf_transformation,[],[f111]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_33,negated_conjecture,
% 27.94/3.99      ( v1_funct_1(sK3) ),
% 27.94/3.99      inference(cnf_transformation,[],[f97]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_395,plain,
% 27.94/3.99      ( ~ v1_relat_1(X0)
% 27.94/3.99      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k1_relat_1(X0)
% 27.94/3.99      | k6_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
% 27.94/3.99      | sK3 != X0 ),
% 27.94/3.99      inference(resolution_lifted,[status(thm)],[c_27,c_33]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_396,plain,
% 27.94/3.99      ( ~ v1_relat_1(sK3)
% 27.94/3.99      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(sK3)
% 27.94/3.99      | k6_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
% 27.94/3.99      inference(unflattening,[status(thm)],[c_395]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_1545,plain,
% 27.94/3.99      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(sK3)
% 27.94/3.99      | k6_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
% 27.94/3.99      | v1_relat_1(sK3) != iProver_top ),
% 27.94/3.99      inference(predicate_to_equality,[status(thm)],[c_396]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_106713,plain,
% 27.94/3.99      ( k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
% 27.94/3.99      | k1_relat_1(sK3) = k1_xboole_0
% 27.94/3.99      | v1_relat_1(sK3) != iProver_top ),
% 27.94/3.99      inference(superposition,[status(thm)],[c_106538,c_1545]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_107201,plain,
% 27.94/3.99      ( k1_relat_1(sK3) = k1_xboole_0
% 27.94/3.99      | k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) ),
% 27.94/3.99      inference(global_propositional_subsumption,
% 27.94/3.99                [status(thm)],
% 27.94/3.99                [c_106713,c_3026]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_107202,plain,
% 27.94/3.99      ( k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
% 27.94/3.99      | k1_relat_1(sK3) = k1_xboole_0 ),
% 27.94/3.99      inference(renaming,[status(thm)],[c_107201]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_29,plain,
% 27.94/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.94/3.99      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 27.94/3.99      inference(cnf_transformation,[],[f96]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_1551,plain,
% 27.94/3.99      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 27.94/3.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 27.94/3.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_4180,plain,
% 27.94/3.99      ( k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
% 27.94/3.99      inference(superposition,[status(thm)],[c_1549,c_1551]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_30,negated_conjecture,
% 27.94/3.99      ( ~ r1_tarski(k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
% 27.94/3.99      inference(cnf_transformation,[],[f112]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_1550,plain,
% 27.94/3.99      ( r1_tarski(k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 27.94/3.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_4343,plain,
% 27.94/3.99      ( r1_tarski(k9_relat_1(sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 27.94/3.99      inference(demodulation,[status(thm)],[c_4180,c_1550]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_107221,plain,
% 27.94/3.99      ( k1_relat_1(sK3) = k1_xboole_0
% 27.94/3.99      | r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) != iProver_top ),
% 27.94/3.99      inference(superposition,[status(thm)],[c_107202,c_4343]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_107591,plain,
% 27.94/3.99      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 27.94/3.99      inference(superposition,[status(thm)],[c_21841,c_107221]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_21,plain,
% 27.94/3.99      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
% 27.94/3.99      | ~ v1_relat_1(X0) ),
% 27.94/3.99      inference(cnf_transformation,[],[f88]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_1554,plain,
% 27.94/3.99      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = iProver_top
% 27.94/3.99      | v1_relat_1(X0) != iProver_top ),
% 27.94/3.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_3480,plain,
% 27.94/3.99      ( r1_tarski(k7_relat_1(sK3,X0),k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),k9_relat_1(sK3,X0))) = iProver_top
% 27.94/3.99      | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
% 27.94/3.99      inference(superposition,[status(thm)],[c_3109,c_1554]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_3707,plain,
% 27.94/3.99      ( k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),k9_relat_1(sK3,X0)) = k7_relat_1(sK3,X0)
% 27.94/3.99      | r1_tarski(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),k9_relat_1(sK3,X0)),k7_relat_1(sK3,X0)) != iProver_top
% 27.94/3.99      | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
% 27.94/3.99      inference(superposition,[status(thm)],[c_3480,c_1569]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_14146,plain,
% 27.94/3.99      ( r1_tarski(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),k9_relat_1(sK3,X0)),k7_relat_1(sK3,X0)) != iProver_top
% 27.94/3.99      | k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),k9_relat_1(sK3,X0)) = k7_relat_1(sK3,X0) ),
% 27.94/3.99      inference(global_propositional_subsumption,
% 27.94/3.99                [status(thm)],
% 27.94/3.99                [c_3707,c_3026,c_4158,c_7423]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_14147,plain,
% 27.94/3.99      ( k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),k9_relat_1(sK3,X0)) = k7_relat_1(sK3,X0)
% 27.94/3.99      | r1_tarski(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),k9_relat_1(sK3,X0)),k7_relat_1(sK3,X0)) != iProver_top ),
% 27.94/3.99      inference(renaming,[status(thm)],[c_14146]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_14157,plain,
% 27.94/3.99      ( k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3))),k9_relat_1(sK3,k1_relat_1(sK3))) = k7_relat_1(sK3,k1_relat_1(sK3))
% 27.94/3.99      | r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),k9_relat_1(sK3,k1_relat_1(sK3))),sK3) != iProver_top ),
% 27.94/3.99      inference(superposition,[status(thm)],[c_9774,c_14147]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_14158,plain,
% 27.94/3.99      ( k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)) = sK3
% 27.94/3.99      | r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)),sK3) != iProver_top ),
% 27.94/3.99      inference(light_normalisation,[status(thm)],[c_14157,c_9774,c_9926]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_108033,plain,
% 27.94/3.99      ( k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3)) = sK3
% 27.94/3.99      | r1_tarski(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3)),sK3) != iProver_top ),
% 27.94/3.99      inference(demodulation,[status(thm)],[c_107591,c_14158]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_9,plain,
% 27.94/3.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 27.94/3.99      inference(cnf_transformation,[],[f117]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_108047,plain,
% 27.94/3.99      ( sK3 = k1_xboole_0 | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 27.94/3.99      inference(demodulation,[status(thm)],[c_108033,c_9]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_24480,plain,
% 27.94/3.99      ( r1_tarski(k1_xboole_0,sK3) ),
% 27.94/3.99      inference(instantiation,[status(thm)],[c_4]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_24481,plain,
% 27.94/3.99      ( r1_tarski(k1_xboole_0,sK3) = iProver_top ),
% 27.94/3.99      inference(predicate_to_equality,[status(thm)],[c_24480]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_109036,plain,
% 27.94/3.99      ( sK3 = k1_xboole_0 ),
% 27.94/3.99      inference(global_propositional_subsumption,
% 27.94/3.99                [status(thm)],
% 27.94/3.99                [c_108047,c_24481]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_109412,plain,
% 27.94/3.99      ( r1_tarski(k9_relat_1(k1_xboole_0,sK2),k6_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
% 27.94/3.99      inference(demodulation,[status(thm)],[c_109036,c_4343]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_25,plain,
% 27.94/3.99      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 27.94/3.99      inference(cnf_transformation,[],[f91]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_4894,plain,
% 27.94/3.99      ( v4_relat_1(k1_xboole_0,X0) = iProver_top
% 27.94/3.99      | r1_tarski(k1_xboole_0,X0) != iProver_top
% 27.94/3.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 27.94/3.99      inference(superposition,[status(thm)],[c_25,c_1559]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_96,plain,
% 27.94/3.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 27.94/3.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_8,plain,
% 27.94/3.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 27.94/3.99      inference(cnf_transformation,[],[f116]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_2297,plain,
% 27.94/3.99      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 27.94/3.99      inference(superposition,[status(thm)],[c_8,c_1557]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_4960,plain,
% 27.94/3.99      ( v4_relat_1(k1_xboole_0,X0) = iProver_top ),
% 27.94/3.99      inference(global_propositional_subsumption,
% 27.94/3.99                [status(thm)],
% 27.94/3.99                [c_4894,c_96,c_2297]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_4966,plain,
% 27.94/3.99      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
% 27.94/3.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 27.94/3.99      inference(superposition,[status(thm)],[c_4960,c_1555]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_4222,plain,
% 27.94/3.99      ( ~ v4_relat_1(k1_xboole_0,X0)
% 27.94/3.99      | ~ v1_relat_1(k1_xboole_0)
% 27.94/3.99      | k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 27.94/3.99      inference(instantiation,[status(thm)],[c_20]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_4223,plain,
% 27.94/3.99      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
% 27.94/3.99      | v4_relat_1(k1_xboole_0,X0) != iProver_top
% 27.94/3.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 27.94/3.99      inference(predicate_to_equality,[status(thm)],[c_4222]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_7945,plain,
% 27.94/3.99      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 27.94/3.99      inference(global_propositional_subsumption,
% 27.94/3.99                [status(thm)],
% 27.94/3.99                [c_4966,c_96,c_2297,c_4223,c_4894]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_2875,plain,
% 27.94/3.99      ( k2_relat_1(k7_relat_1(k1_xboole_0,X0)) = k9_relat_1(k1_xboole_0,X0) ),
% 27.94/3.99      inference(superposition,[status(thm)],[c_2297,c_1556]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_7954,plain,
% 27.94/3.99      ( k9_relat_1(k1_xboole_0,X0) = k2_relat_1(k1_xboole_0) ),
% 27.94/3.99      inference(demodulation,[status(thm)],[c_7945,c_2875]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_24,plain,
% 27.94/3.99      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 27.94/3.99      inference(cnf_transformation,[],[f92]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_7955,plain,
% 27.94/3.99      ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 27.94/3.99      inference(light_normalisation,[status(thm)],[c_7954,c_24]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_109436,plain,
% 27.94/3.99      ( r1_tarski(k1_xboole_0,k6_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
% 27.94/3.99      inference(demodulation,[status(thm)],[c_109412,c_7955]) ).
% 27.94/3.99  
% 27.94/3.99  cnf(c_110456,plain,
% 27.94/3.99      ( $false ),
% 27.94/3.99      inference(superposition,[status(thm)],[c_1566,c_109436]) ).
% 27.94/3.99  
% 27.94/3.99  
% 27.94/3.99  % SZS output end CNFRefutation for theBenchmark.p
% 27.94/3.99  
% 27.94/3.99  ------                               Statistics
% 27.94/3.99  
% 27.94/3.99  ------ General
% 27.94/3.99  
% 27.94/3.99  abstr_ref_over_cycles:                  0
% 27.94/3.99  abstr_ref_under_cycles:                 0
% 27.94/3.99  gc_basic_clause_elim:                   0
% 27.94/3.99  forced_gc_time:                         0
% 27.94/3.99  parsing_time:                           0.01
% 27.94/3.99  unif_index_cands_time:                  0.
% 27.94/3.99  unif_index_add_time:                    0.
% 27.94/3.99  orderings_time:                         0.
% 27.94/3.99  out_proof_time:                         0.03
% 27.94/3.99  total_time:                             3.376
% 27.94/3.99  num_of_symbols:                         53
% 27.94/3.99  num_of_terms:                           67600
% 27.94/3.99  
% 27.94/3.99  ------ Preprocessing
% 27.94/3.99  
% 27.94/3.99  num_of_splits:                          0
% 27.94/3.99  num_of_split_atoms:                     0
% 27.94/3.99  num_of_reused_defs:                     0
% 27.94/3.99  num_eq_ax_congr_red:                    30
% 27.94/3.99  num_of_sem_filtered_clauses:            1
% 27.94/3.99  num_of_subtypes:                        0
% 27.94/3.99  monotx_restored_types:                  0
% 27.94/3.99  sat_num_of_epr_types:                   0
% 27.94/3.99  sat_num_of_non_cyclic_types:            0
% 27.94/3.99  sat_guarded_non_collapsed_types:        0
% 27.94/3.99  num_pure_diseq_elim:                    0
% 27.94/3.99  simp_replaced_by:                       0
% 27.94/3.99  res_preprocessed:                       158
% 27.94/3.99  prep_upred:                             0
% 27.94/3.99  prep_unflattend:                        11
% 27.94/3.99  smt_new_axioms:                         0
% 27.94/3.99  pred_elim_cands:                        5
% 27.94/3.99  pred_elim:                              1
% 27.94/3.99  pred_elim_cl:                           1
% 27.94/3.99  pred_elim_cycles:                       7
% 27.94/3.99  merged_defs:                            24
% 27.94/3.99  merged_defs_ncl:                        0
% 27.94/3.99  bin_hyper_res:                          25
% 27.94/3.99  prep_cycles:                            4
% 27.94/3.99  pred_elim_time:                         0.005
% 27.94/3.99  splitting_time:                         0.
% 27.94/3.99  sem_filter_time:                        0.
% 27.94/3.99  monotx_time:                            0.
% 27.94/3.99  subtype_inf_time:                       0.
% 27.94/3.99  
% 27.94/3.99  ------ Problem properties
% 27.94/3.99  
% 27.94/3.99  clauses:                                32
% 27.94/3.99  conjectures:                            3
% 27.94/3.99  epr:                                    5
% 27.94/3.99  horn:                                   30
% 27.94/3.99  ground:                                 5
% 27.94/3.99  unary:                                  11
% 27.94/3.99  binary:                                 12
% 27.94/3.99  lits:                                   62
% 27.94/3.99  lits_eq:                                18
% 27.94/3.99  fd_pure:                                0
% 27.94/3.99  fd_pseudo:                              0
% 27.94/3.99  fd_cond:                                1
% 27.94/3.99  fd_pseudo_cond:                         1
% 27.94/3.99  ac_symbols:                             0
% 27.94/3.99  
% 27.94/3.99  ------ Propositional Solver
% 27.94/3.99  
% 27.94/3.99  prop_solver_calls:                      46
% 27.94/3.99  prop_fast_solver_calls:                 4036
% 27.94/3.99  smt_solver_calls:                       0
% 27.94/3.99  smt_fast_solver_calls:                  0
% 27.94/3.99  prop_num_of_clauses:                    45798
% 27.94/3.99  prop_preprocess_simplified:             88894
% 27.94/3.99  prop_fo_subsumed:                       225
% 27.94/3.99  prop_solver_time:                       0.
% 27.94/3.99  smt_solver_time:                        0.
% 27.94/3.99  smt_fast_solver_time:                   0.
% 27.94/3.99  prop_fast_solver_time:                  0.
% 27.94/3.99  prop_unsat_core_time:                   0.
% 27.94/3.99  
% 27.94/3.99  ------ QBF
% 27.94/3.99  
% 27.94/3.99  qbf_q_res:                              0
% 27.94/3.99  qbf_num_tautologies:                    0
% 27.94/3.99  qbf_prep_cycles:                        0
% 27.94/3.99  
% 27.94/3.99  ------ BMC1
% 27.94/3.99  
% 27.94/3.99  bmc1_current_bound:                     -1
% 27.94/3.99  bmc1_last_solved_bound:                 -1
% 27.94/3.99  bmc1_unsat_core_size:                   -1
% 27.94/3.99  bmc1_unsat_core_parents_size:           -1
% 27.94/3.99  bmc1_merge_next_fun:                    0
% 27.94/3.99  bmc1_unsat_core_clauses_time:           0.
% 27.94/3.99  
% 27.94/3.99  ------ Instantiation
% 27.94/3.99  
% 27.94/3.99  inst_num_of_clauses:                    4460
% 27.94/3.99  inst_num_in_passive:                    1708
% 27.94/3.99  inst_num_in_active:                     4190
% 27.94/3.99  inst_num_in_unprocessed:                1056
% 27.94/3.99  inst_num_of_loops:                      4739
% 27.94/3.99  inst_num_of_learning_restarts:          1
% 27.94/3.99  inst_num_moves_active_passive:          547
% 27.94/3.99  inst_lit_activity:                      0
% 27.94/3.99  inst_lit_activity_moves:                1
% 27.94/3.99  inst_num_tautologies:                   0
% 27.94/3.99  inst_num_prop_implied:                  0
% 27.94/3.99  inst_num_existing_simplified:           0
% 27.94/3.99  inst_num_eq_res_simplified:             0
% 27.94/3.99  inst_num_child_elim:                    0
% 27.94/3.99  inst_num_of_dismatching_blockings:      8437
% 27.94/3.99  inst_num_of_non_proper_insts:           15151
% 27.94/3.99  inst_num_of_duplicates:                 0
% 27.94/3.99  inst_inst_num_from_inst_to_res:         0
% 27.94/3.99  inst_dismatching_checking_time:         0.
% 27.94/3.99  
% 27.94/3.99  ------ Resolution
% 27.94/3.99  
% 27.94/3.99  res_num_of_clauses:                     46
% 27.94/3.99  res_num_in_passive:                     46
% 27.94/3.99  res_num_in_active:                      0
% 27.94/3.99  res_num_of_loops:                       162
% 27.94/3.99  res_forward_subset_subsumed:            1401
% 27.94/3.99  res_backward_subset_subsumed:           4
% 27.94/3.99  res_forward_subsumed:                   0
% 27.94/3.99  res_backward_subsumed:                  0
% 27.94/3.99  res_forward_subsumption_resolution:     0
% 27.94/3.99  res_backward_subsumption_resolution:    0
% 27.94/3.99  res_clause_to_clause_subsumption:       17638
% 27.94/3.99  res_orphan_elimination:                 0
% 27.94/3.99  res_tautology_del:                      1018
% 27.94/3.99  res_num_eq_res_simplified:              0
% 27.94/3.99  res_num_sel_changes:                    0
% 27.94/3.99  res_moves_from_active_to_pass:          0
% 27.94/3.99  
% 27.94/3.99  ------ Superposition
% 27.94/3.99  
% 27.94/3.99  sup_time_total:                         0.
% 27.94/3.99  sup_time_generating:                    0.
% 27.94/3.99  sup_time_sim_full:                      0.
% 27.94/3.99  sup_time_sim_immed:                     0.
% 27.94/3.99  
% 27.94/3.99  sup_num_of_clauses:                     2891
% 27.94/3.99  sup_num_in_active:                      232
% 27.94/3.99  sup_num_in_passive:                     2659
% 27.94/3.99  sup_num_of_loops:                       946
% 27.94/3.99  sup_fw_superposition:                   3379
% 27.94/3.99  sup_bw_superposition:                   3094
% 27.94/3.99  sup_immediate_simplified:               3457
% 27.94/3.99  sup_given_eliminated:                   13
% 27.94/3.99  comparisons_done:                       0
% 27.94/3.99  comparisons_avoided:                    321
% 27.94/3.99  
% 27.94/3.99  ------ Simplifications
% 27.94/3.99  
% 27.94/3.99  
% 27.94/3.99  sim_fw_subset_subsumed:                 354
% 27.94/3.99  sim_bw_subset_subsumed:                 79
% 27.94/3.99  sim_fw_subsumed:                        740
% 27.94/3.99  sim_bw_subsumed:                        58
% 27.94/3.99  sim_fw_subsumption_res:                 0
% 27.94/3.99  sim_bw_subsumption_res:                 0
% 27.94/3.99  sim_tautology_del:                      160
% 27.94/3.99  sim_eq_tautology_del:                   964
% 27.94/3.99  sim_eq_res_simp:                        2
% 27.94/3.99  sim_fw_demodulated:                     1455
% 27.94/3.99  sim_bw_demodulated:                     711
% 27.94/3.99  sim_light_normalised:                   2017
% 27.94/3.99  sim_joinable_taut:                      0
% 27.94/3.99  sim_joinable_simp:                      0
% 27.94/3.99  sim_ac_normalised:                      0
% 27.94/3.99  sim_smt_subsumption:                    0
% 27.94/3.99  
%------------------------------------------------------------------------------
