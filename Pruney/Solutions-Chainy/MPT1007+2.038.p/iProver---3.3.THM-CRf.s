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
% DateTime   : Thu Dec  3 12:04:49 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :  176 ( 911 expanded)
%              Number of clauses        :   89 ( 186 expanded)
%              Number of leaves         :   26 ( 233 expanded)
%              Depth                    :   28
%              Number of atoms          :  458 (2217 expanded)
%              Number of equality atoms :  201 ( 939 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5,X6] :
                  ( ( r2_hidden(X6,X1)
                    & r2_hidden(X5,X6)
                    & r2_hidden(X4,X5)
                    & r2_hidden(X3,X4)
                    & r2_hidden(X2,X3) )
                 => r1_xboole_0(X2,X0) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f24])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f46])).

fof(f74,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f22,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f39,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f40,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f49,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( ~ r2_hidden(k1_funct_1(sK4,sK2),sK3)
      & k1_xboole_0 != sK3
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))
      & v1_funct_2(sK4,k1_tarski(sK2),sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ~ r2_hidden(k1_funct_1(sK4,sK2),sK3)
    & k1_xboole_0 != sK3
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))
    & v1_funct_2(sK4,k1_tarski(sK2),sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f40,f49])).

fof(f85,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) ),
    inference(cnf_transformation,[],[f50])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f88,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f60,f61])).

fof(f89,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f59,f88])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f58,f89])).

fof(f91,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f57,f90])).

fof(f92,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f56,f91])).

fof(f93,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f55,f92])).

fof(f97,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) ),
    inference(definition_unfolding,[],[f85,f93])).

fof(f84,plain,(
    v1_funct_2(sK4,k1_tarski(sK2),sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f98,plain,(
    v1_funct_2(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) ),
    inference(definition_unfolding,[],[f84,f93])).

fof(f21,axiom,(
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
    inference(ennf_transformation,[],[f21])).

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
    inference(flattening,[],[f37])).

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
    inference(nnf_transformation,[],[f38])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f86,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f50])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3))
     => ( r2_hidden(k2_mcart_1(X0),X3)
        & ( k1_mcart_1(X0) = X2
          | k1_mcart_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k2_mcart_1(X0),X3)
        & ( k1_mcart_1(X0) = X2
          | k1_mcart_1(X0) = X1 ) )
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(X0) = X2
      | k1_mcart_1(X0) = X1
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(X0) = X2
      | k1_mcart_1(X0) = X1
      | ~ r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),X3)) ) ),
    inference(definition_unfolding,[],[f72,f92])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r2_hidden(X1,X0)
         => ( r2_hidden(k2_mcart_1(X1),k2_relat_1(X0))
            & r2_hidden(k1_mcart_1(X1),k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(k2_mcart_1(X1),k2_relat_1(X0))
            & r2_hidden(k1_mcart_1(X1),k1_relat_1(X0)) )
          | ~ r2_hidden(X1,X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_mcart_1(X1),k1_relat_1(X0))
      | ~ r2_hidden(X1,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r2_hidden(k2_mcart_1(X1),k2_relat_1(X0))
      | ~ r2_hidden(X1,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f83,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f50])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f41])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f87,plain,(
    ~ r2_hidden(k1_funct_1(sK4,sK2),sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : ~ v1_xboole_0(k3_enumset1(X0,X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] : ~ v1_xboole_0(k3_enumset1(X0,X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f10])).

fof(f94,plain,(
    ! [X4,X2,X0,X3,X1] : ~ v1_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) ),
    inference(definition_unfolding,[],[f62,f89])).

fof(f13,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_16,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1264,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_459,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(X2)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_27])).

cnf(c_460,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(X1) ),
    inference(unflattening,[status(thm)],[c_459])).

cnf(c_1262,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(X0)
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X1,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_460])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_486,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_27])).

cnf(c_487,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | k1_relset_1(X0,X1,sK4) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_486])).

cnf(c_762,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != X0
    | k1_relset_1(X0,X1,sK4) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK3 != X1
    | sK4 != sK4
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_487])).

cnf(c_763,plain,
    ( k1_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_762])).

cnf(c_26,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_764,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))
    | k1_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_763,c_26])).

cnf(c_765,plain,
    ( k1_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) ),
    inference(renaming,[status(thm)],[c_764])).

cnf(c_814,plain,
    ( k1_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(equality_resolution_simp,[status(thm)],[c_765])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_522,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_27])).

cnf(c_523,plain,
    ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_522])).

cnf(c_1416,plain,
    ( k1_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4) = k1_relat_1(sK4) ),
    inference(equality_resolution,[status(thm)],[c_523])).

cnf(c_1429,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_relat_1(sK4) ),
    inference(light_normalisation,[status(thm)],[c_814,c_1416])).

cnf(c_1646,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3)) != k1_zfmisc_1(X0)
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X1,sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1262,c_1429])).

cnf(c_1653,plain,
    ( r2_hidden(X0,k2_zfmisc_1(k1_relat_1(sK4),sK3)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1646])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),X3))
    | k1_mcart_1(X0) = X2
    | k1_mcart_1(X0) = X1 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1265,plain,
    ( k1_mcart_1(X0) = X1
    | k1_mcart_1(X0) = X2
    | r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2036,plain,
    ( k1_mcart_1(X0) = sK2
    | r2_hidden(X0,k2_zfmisc_1(k1_relat_1(sK4),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1429,c_1265])).

cnf(c_2767,plain,
    ( k1_mcart_1(X0) = sK2
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1653,c_2036])).

cnf(c_3549,plain,
    ( k1_mcart_1(sK1(sK4)) = sK2
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1264,c_2767])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k1_mcart_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_531,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_27])).

cnf(c_532,plain,
    ( v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_531])).

cnf(c_712,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k1_mcart_1(X0),k1_relat_1(X1))
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_532])).

cnf(c_713,plain,
    ( ~ r2_hidden(X0,sK4)
    | r2_hidden(k1_mcart_1(X0),k1_relat_1(sK4))
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
    inference(unflattening,[status(thm)],[c_712])).

cnf(c_943,plain,
    ( ~ r2_hidden(X0,sK4)
    | r2_hidden(k1_mcart_1(X0),k1_relat_1(sK4))
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_713])).

cnf(c_1256,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(k1_mcart_1(X0),k1_relat_1(sK4)) = iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_943])).

cnf(c_944,plain,
    ( sP2_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_713])).

cnf(c_977,plain,
    ( sP2_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_944])).

cnf(c_978,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(k1_mcart_1(X0),k1_relat_1(sK4)) = iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_943])).

cnf(c_948,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1403,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) ),
    inference(instantiation,[status(thm)],[c_948])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k2_mcart_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_727,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k2_mcart_1(X0),k2_relat_1(X1))
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_532])).

cnf(c_728,plain,
    ( ~ r2_hidden(X0,sK4)
    | r2_hidden(k2_mcart_1(X0),k2_relat_1(sK4))
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
    inference(unflattening,[status(thm)],[c_727])).

cnf(c_940,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_728])).

cnf(c_1460,plain,
    ( ~ sP0_iProver_split
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) ),
    inference(instantiation,[status(thm)],[c_940])).

cnf(c_1462,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1460])).

cnf(c_1836,plain,
    ( r2_hidden(k1_mcart_1(X0),k1_relat_1(sK4)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1256,c_977,c_978,c_1403,c_1462])).

cnf(c_1837,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(k1_mcart_1(X0),k1_relat_1(sK4)) = iProver_top ),
    inference(renaming,[status(thm)],[c_1836])).

cnf(c_3856,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK1(sK4),sK4) != iProver_top
    | r2_hidden(sK2,k1_relat_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3549,c_1837])).

cnf(c_12,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_7,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_334,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_12,c_7])).

cnf(c_338,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_334,c_11])).

cnf(c_339,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_338])).

cnf(c_474,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X2,X1))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_339,c_27])).

cnf(c_475,plain,
    ( r1_tarski(k2_relat_1(sK4),X0)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X1,X0)) ),
    inference(unflattening,[status(thm)],[c_474])).

cnf(c_1404,plain,
    ( r1_tarski(k2_relat_1(sK4),sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) ),
    inference(instantiation,[status(thm)],[c_475])).

cnf(c_1405,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))
    | r1_tarski(k2_relat_1(sK4),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1404])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_315,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_29])).

cnf(c_316,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_315])).

cnf(c_698,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4))
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
    inference(resolution,[status(thm)],[c_532,c_316])).

cnf(c_945,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4))
    | ~ sP3_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP3_iProver_split])],[c_698])).

cnf(c_1259,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top
    | sP3_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_945])).

cnf(c_946,plain,
    ( sP3_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_698])).

cnf(c_982,plain,
    ( sP3_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_946])).

cnf(c_983,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top
    | sP3_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_945])).

cnf(c_1937,plain,
    ( r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1259,c_982,c_983,c_1403,c_1462])).

cnf(c_1938,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top ),
    inference(renaming,[status(thm)],[c_1937])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1267,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2131,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),X1) = iProver_top
    | r1_tarski(k2_relat_1(sK4),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1938,c_1267])).

cnf(c_25,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(sK4,sK2),sK3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1263,plain,
    ( r2_hidden(k1_funct_1(sK4,sK2),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3289,plain,
    ( r2_hidden(sK2,k1_relat_1(sK4)) != iProver_top
    | r1_tarski(k2_relat_1(sK4),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2131,c_1263])).

cnf(c_4028,plain,
    ( r2_hidden(sK1(sK4),sK4) != iProver_top
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3856,c_1403,c_1405,c_3289])).

cnf(c_4029,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK1(sK4),sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_4028])).

cnf(c_4034,plain,
    ( sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1264,c_4029])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_4,plain,
    ( ~ v1_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_309,plain,
    ( k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_4])).

cnf(c_1524,plain,
    ( k1_relat_1(sK4) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1429,c_309])).

cnf(c_4163,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4034,c_1524])).

cnf(c_9,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_4214,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4163,c_9])).

cnf(c_4215,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_4214])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:57:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.71/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/0.98  
% 2.71/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.71/0.98  
% 2.71/0.98  ------  iProver source info
% 2.71/0.98  
% 2.71/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.71/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.71/0.98  git: non_committed_changes: false
% 2.71/0.98  git: last_make_outside_of_git: false
% 2.71/0.98  
% 2.71/0.98  ------ 
% 2.71/0.98  
% 2.71/0.98  ------ Input Options
% 2.71/0.98  
% 2.71/0.98  --out_options                           all
% 2.71/0.98  --tptp_safe_out                         true
% 2.71/0.98  --problem_path                          ""
% 2.71/0.98  --include_path                          ""
% 2.71/0.98  --clausifier                            res/vclausify_rel
% 2.71/0.98  --clausifier_options                    --mode clausify
% 2.71/0.98  --stdin                                 false
% 2.71/0.98  --stats_out                             all
% 2.71/0.98  
% 2.71/0.98  ------ General Options
% 2.71/0.98  
% 2.71/0.98  --fof                                   false
% 2.71/0.98  --time_out_real                         305.
% 2.71/0.98  --time_out_virtual                      -1.
% 2.71/0.98  --symbol_type_check                     false
% 2.71/0.98  --clausify_out                          false
% 2.71/0.98  --sig_cnt_out                           false
% 2.71/0.98  --trig_cnt_out                          false
% 2.71/0.98  --trig_cnt_out_tolerance                1.
% 2.71/0.98  --trig_cnt_out_sk_spl                   false
% 2.71/0.98  --abstr_cl_out                          false
% 2.71/0.98  
% 2.71/0.98  ------ Global Options
% 2.71/0.98  
% 2.71/0.98  --schedule                              default
% 2.71/0.98  --add_important_lit                     false
% 2.71/0.98  --prop_solver_per_cl                    1000
% 2.71/0.98  --min_unsat_core                        false
% 2.71/0.98  --soft_assumptions                      false
% 2.71/0.98  --soft_lemma_size                       3
% 2.71/0.98  --prop_impl_unit_size                   0
% 2.71/0.98  --prop_impl_unit                        []
% 2.71/0.98  --share_sel_clauses                     true
% 2.71/0.98  --reset_solvers                         false
% 2.71/0.98  --bc_imp_inh                            [conj_cone]
% 2.71/0.98  --conj_cone_tolerance                   3.
% 2.71/0.98  --extra_neg_conj                        none
% 2.71/0.98  --large_theory_mode                     true
% 2.71/0.98  --prolific_symb_bound                   200
% 2.71/0.98  --lt_threshold                          2000
% 2.71/0.98  --clause_weak_htbl                      true
% 2.71/0.98  --gc_record_bc_elim                     false
% 2.71/0.98  
% 2.71/0.98  ------ Preprocessing Options
% 2.71/0.98  
% 2.71/0.98  --preprocessing_flag                    true
% 2.71/0.98  --time_out_prep_mult                    0.1
% 2.71/0.98  --splitting_mode                        input
% 2.71/0.98  --splitting_grd                         true
% 2.71/0.98  --splitting_cvd                         false
% 2.71/0.98  --splitting_cvd_svl                     false
% 2.71/0.98  --splitting_nvd                         32
% 2.71/0.98  --sub_typing                            true
% 2.71/0.98  --prep_gs_sim                           true
% 2.71/0.98  --prep_unflatten                        true
% 2.71/0.98  --prep_res_sim                          true
% 2.71/0.98  --prep_upred                            true
% 2.71/0.98  --prep_sem_filter                       exhaustive
% 2.71/0.98  --prep_sem_filter_out                   false
% 2.71/0.98  --pred_elim                             true
% 2.71/0.98  --res_sim_input                         true
% 2.71/0.98  --eq_ax_congr_red                       true
% 2.71/0.98  --pure_diseq_elim                       true
% 2.71/0.98  --brand_transform                       false
% 2.71/0.98  --non_eq_to_eq                          false
% 2.71/0.98  --prep_def_merge                        true
% 2.71/0.98  --prep_def_merge_prop_impl              false
% 2.71/0.98  --prep_def_merge_mbd                    true
% 2.71/0.98  --prep_def_merge_tr_red                 false
% 2.71/0.98  --prep_def_merge_tr_cl                  false
% 2.71/0.98  --smt_preprocessing                     true
% 2.71/0.98  --smt_ac_axioms                         fast
% 2.71/0.98  --preprocessed_out                      false
% 2.71/0.98  --preprocessed_stats                    false
% 2.71/0.98  
% 2.71/0.98  ------ Abstraction refinement Options
% 2.71/0.98  
% 2.71/0.98  --abstr_ref                             []
% 2.71/0.98  --abstr_ref_prep                        false
% 2.71/0.98  --abstr_ref_until_sat                   false
% 2.71/0.98  --abstr_ref_sig_restrict                funpre
% 2.71/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.71/0.98  --abstr_ref_under                       []
% 2.71/0.98  
% 2.71/0.98  ------ SAT Options
% 2.71/0.98  
% 2.71/0.98  --sat_mode                              false
% 2.71/0.98  --sat_fm_restart_options                ""
% 2.71/0.98  --sat_gr_def                            false
% 2.71/0.98  --sat_epr_types                         true
% 2.71/0.98  --sat_non_cyclic_types                  false
% 2.71/0.98  --sat_finite_models                     false
% 2.71/0.98  --sat_fm_lemmas                         false
% 2.71/0.98  --sat_fm_prep                           false
% 2.71/0.98  --sat_fm_uc_incr                        true
% 2.71/0.98  --sat_out_model                         small
% 2.71/0.98  --sat_out_clauses                       false
% 2.71/0.98  
% 2.71/0.98  ------ QBF Options
% 2.71/0.98  
% 2.71/0.98  --qbf_mode                              false
% 2.71/0.98  --qbf_elim_univ                         false
% 2.71/0.98  --qbf_dom_inst                          none
% 2.71/0.98  --qbf_dom_pre_inst                      false
% 2.71/0.98  --qbf_sk_in                             false
% 2.71/0.98  --qbf_pred_elim                         true
% 2.71/0.98  --qbf_split                             512
% 2.71/0.98  
% 2.71/0.98  ------ BMC1 Options
% 2.71/0.98  
% 2.71/0.98  --bmc1_incremental                      false
% 2.71/0.98  --bmc1_axioms                           reachable_all
% 2.71/0.98  --bmc1_min_bound                        0
% 2.71/0.98  --bmc1_max_bound                        -1
% 2.71/0.98  --bmc1_max_bound_default                -1
% 2.71/0.98  --bmc1_symbol_reachability              true
% 2.71/0.98  --bmc1_property_lemmas                  false
% 2.71/0.98  --bmc1_k_induction                      false
% 2.71/0.98  --bmc1_non_equiv_states                 false
% 2.71/0.98  --bmc1_deadlock                         false
% 2.71/0.98  --bmc1_ucm                              false
% 2.71/0.98  --bmc1_add_unsat_core                   none
% 2.71/0.98  --bmc1_unsat_core_children              false
% 2.71/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.71/0.98  --bmc1_out_stat                         full
% 2.71/0.98  --bmc1_ground_init                      false
% 2.71/0.98  --bmc1_pre_inst_next_state              false
% 2.71/0.98  --bmc1_pre_inst_state                   false
% 2.71/0.98  --bmc1_pre_inst_reach_state             false
% 2.71/0.98  --bmc1_out_unsat_core                   false
% 2.71/0.98  --bmc1_aig_witness_out                  false
% 2.71/0.98  --bmc1_verbose                          false
% 2.71/0.98  --bmc1_dump_clauses_tptp                false
% 2.71/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.71/0.98  --bmc1_dump_file                        -
% 2.71/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.71/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.71/0.98  --bmc1_ucm_extend_mode                  1
% 2.71/0.98  --bmc1_ucm_init_mode                    2
% 2.71/0.98  --bmc1_ucm_cone_mode                    none
% 2.71/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.71/0.98  --bmc1_ucm_relax_model                  4
% 2.71/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.71/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.71/0.98  --bmc1_ucm_layered_model                none
% 2.71/0.98  --bmc1_ucm_max_lemma_size               10
% 2.71/0.98  
% 2.71/0.98  ------ AIG Options
% 2.71/0.98  
% 2.71/0.98  --aig_mode                              false
% 2.71/0.98  
% 2.71/0.98  ------ Instantiation Options
% 2.71/0.98  
% 2.71/0.98  --instantiation_flag                    true
% 2.71/0.98  --inst_sos_flag                         false
% 2.71/0.98  --inst_sos_phase                        true
% 2.71/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.71/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.71/0.98  --inst_lit_sel_side                     num_symb
% 2.71/0.98  --inst_solver_per_active                1400
% 2.71/0.98  --inst_solver_calls_frac                1.
% 2.71/0.98  --inst_passive_queue_type               priority_queues
% 2.71/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.71/0.98  --inst_passive_queues_freq              [25;2]
% 2.71/0.98  --inst_dismatching                      true
% 2.71/0.98  --inst_eager_unprocessed_to_passive     true
% 2.71/0.98  --inst_prop_sim_given                   true
% 2.71/0.98  --inst_prop_sim_new                     false
% 2.71/0.98  --inst_subs_new                         false
% 2.71/0.98  --inst_eq_res_simp                      false
% 2.71/0.98  --inst_subs_given                       false
% 2.71/0.98  --inst_orphan_elimination               true
% 2.71/0.98  --inst_learning_loop_flag               true
% 2.71/0.98  --inst_learning_start                   3000
% 2.71/0.98  --inst_learning_factor                  2
% 2.71/0.98  --inst_start_prop_sim_after_learn       3
% 2.71/0.98  --inst_sel_renew                        solver
% 2.71/0.98  --inst_lit_activity_flag                true
% 2.71/0.98  --inst_restr_to_given                   false
% 2.71/0.98  --inst_activity_threshold               500
% 2.71/0.98  --inst_out_proof                        true
% 2.71/0.98  
% 2.71/0.98  ------ Resolution Options
% 2.71/0.98  
% 2.71/0.98  --resolution_flag                       true
% 2.71/0.98  --res_lit_sel                           adaptive
% 2.71/0.98  --res_lit_sel_side                      none
% 2.71/0.98  --res_ordering                          kbo
% 2.71/0.98  --res_to_prop_solver                    active
% 2.71/0.98  --res_prop_simpl_new                    false
% 2.71/0.98  --res_prop_simpl_given                  true
% 2.71/0.98  --res_passive_queue_type                priority_queues
% 2.71/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.71/0.98  --res_passive_queues_freq               [15;5]
% 2.71/0.98  --res_forward_subs                      full
% 2.71/0.98  --res_backward_subs                     full
% 2.71/0.98  --res_forward_subs_resolution           true
% 2.71/0.98  --res_backward_subs_resolution          true
% 2.71/0.98  --res_orphan_elimination                true
% 2.71/0.98  --res_time_limit                        2.
% 2.71/0.98  --res_out_proof                         true
% 2.71/0.98  
% 2.71/0.98  ------ Superposition Options
% 2.71/0.98  
% 2.71/0.98  --superposition_flag                    true
% 2.71/0.98  --sup_passive_queue_type                priority_queues
% 2.71/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.71/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.71/0.98  --demod_completeness_check              fast
% 2.71/0.98  --demod_use_ground                      true
% 2.71/0.98  --sup_to_prop_solver                    passive
% 2.71/0.98  --sup_prop_simpl_new                    true
% 2.71/0.98  --sup_prop_simpl_given                  true
% 2.71/0.98  --sup_fun_splitting                     false
% 2.71/0.98  --sup_smt_interval                      50000
% 2.71/0.98  
% 2.71/0.98  ------ Superposition Simplification Setup
% 2.71/0.98  
% 2.71/0.98  --sup_indices_passive                   []
% 2.71/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.71/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.71/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.71/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.71/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.71/0.98  --sup_full_bw                           [BwDemod]
% 2.71/0.98  --sup_immed_triv                        [TrivRules]
% 2.71/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.71/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.71/0.98  --sup_immed_bw_main                     []
% 2.71/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.71/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.71/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.71/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.71/0.98  
% 2.71/0.98  ------ Combination Options
% 2.71/0.98  
% 2.71/0.98  --comb_res_mult                         3
% 2.71/0.98  --comb_sup_mult                         2
% 2.71/0.98  --comb_inst_mult                        10
% 2.71/0.98  
% 2.71/0.98  ------ Debug Options
% 2.71/0.98  
% 2.71/0.98  --dbg_backtrace                         false
% 2.71/0.98  --dbg_dump_prop_clauses                 false
% 2.71/0.98  --dbg_dump_prop_clauses_file            -
% 2.71/0.98  --dbg_out_stat                          false
% 2.71/0.98  ------ Parsing...
% 2.71/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.71/0.98  
% 2.71/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.71/0.98  
% 2.71/0.98  ------ Preprocessing... gs_s  sp: 6 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.71/0.98  
% 2.71/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.71/0.98  ------ Proving...
% 2.71/0.98  ------ Problem Properties 
% 2.71/0.98  
% 2.71/0.98  
% 2.71/0.98  clauses                                 25
% 2.71/0.98  conjectures                             2
% 2.71/0.98  EPR                                     5
% 2.71/0.98  Horn                                    18
% 2.71/0.98  unary                                   6
% 2.71/0.98  binary                                  12
% 2.71/0.98  lits                                    52
% 2.71/0.98  lits eq                                 19
% 2.71/0.98  fd_pure                                 0
% 2.71/0.98  fd_pseudo                               0
% 2.71/0.98  fd_cond                                 1
% 2.71/0.98  fd_pseudo_cond                          1
% 2.71/0.98  AC symbols                              0
% 2.71/0.98  
% 2.71/0.98  ------ Schedule dynamic 5 is on 
% 2.71/0.98  
% 2.71/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.71/0.98  
% 2.71/0.98  
% 2.71/0.98  ------ 
% 2.71/0.98  Current options:
% 2.71/0.98  ------ 
% 2.71/0.98  
% 2.71/0.98  ------ Input Options
% 2.71/0.98  
% 2.71/0.98  --out_options                           all
% 2.71/0.98  --tptp_safe_out                         true
% 2.71/0.98  --problem_path                          ""
% 2.71/0.98  --include_path                          ""
% 2.71/0.98  --clausifier                            res/vclausify_rel
% 2.71/0.98  --clausifier_options                    --mode clausify
% 2.71/0.98  --stdin                                 false
% 2.71/0.98  --stats_out                             all
% 2.71/0.98  
% 2.71/0.98  ------ General Options
% 2.71/0.98  
% 2.71/0.98  --fof                                   false
% 2.71/0.98  --time_out_real                         305.
% 2.71/0.98  --time_out_virtual                      -1.
% 2.71/0.98  --symbol_type_check                     false
% 2.71/0.98  --clausify_out                          false
% 2.71/0.98  --sig_cnt_out                           false
% 2.71/0.98  --trig_cnt_out                          false
% 2.71/0.98  --trig_cnt_out_tolerance                1.
% 2.71/0.98  --trig_cnt_out_sk_spl                   false
% 2.71/0.98  --abstr_cl_out                          false
% 2.71/0.98  
% 2.71/0.98  ------ Global Options
% 2.71/0.98  
% 2.71/0.98  --schedule                              default
% 2.71/0.98  --add_important_lit                     false
% 2.71/0.98  --prop_solver_per_cl                    1000
% 2.71/0.98  --min_unsat_core                        false
% 2.71/0.98  --soft_assumptions                      false
% 2.71/0.98  --soft_lemma_size                       3
% 2.71/0.98  --prop_impl_unit_size                   0
% 2.71/0.98  --prop_impl_unit                        []
% 2.71/0.98  --share_sel_clauses                     true
% 2.71/0.98  --reset_solvers                         false
% 2.71/0.98  --bc_imp_inh                            [conj_cone]
% 2.71/0.98  --conj_cone_tolerance                   3.
% 2.71/0.98  --extra_neg_conj                        none
% 2.71/0.98  --large_theory_mode                     true
% 2.71/0.98  --prolific_symb_bound                   200
% 2.71/0.98  --lt_threshold                          2000
% 2.71/0.98  --clause_weak_htbl                      true
% 2.71/0.98  --gc_record_bc_elim                     false
% 2.71/0.98  
% 2.71/0.98  ------ Preprocessing Options
% 2.71/0.98  
% 2.71/0.98  --preprocessing_flag                    true
% 2.71/0.98  --time_out_prep_mult                    0.1
% 2.71/0.98  --splitting_mode                        input
% 2.71/0.98  --splitting_grd                         true
% 2.71/0.98  --splitting_cvd                         false
% 2.71/0.98  --splitting_cvd_svl                     false
% 2.71/0.98  --splitting_nvd                         32
% 2.71/0.98  --sub_typing                            true
% 2.71/0.98  --prep_gs_sim                           true
% 2.71/0.98  --prep_unflatten                        true
% 2.71/0.98  --prep_res_sim                          true
% 2.71/0.98  --prep_upred                            true
% 2.71/0.98  --prep_sem_filter                       exhaustive
% 2.71/0.98  --prep_sem_filter_out                   false
% 2.71/0.98  --pred_elim                             true
% 2.71/0.98  --res_sim_input                         true
% 2.71/0.98  --eq_ax_congr_red                       true
% 2.71/0.98  --pure_diseq_elim                       true
% 2.71/0.98  --brand_transform                       false
% 2.71/0.98  --non_eq_to_eq                          false
% 2.71/0.98  --prep_def_merge                        true
% 2.71/0.98  --prep_def_merge_prop_impl              false
% 2.71/0.98  --prep_def_merge_mbd                    true
% 2.71/0.98  --prep_def_merge_tr_red                 false
% 2.71/0.98  --prep_def_merge_tr_cl                  false
% 2.71/0.98  --smt_preprocessing                     true
% 2.71/0.98  --smt_ac_axioms                         fast
% 2.71/0.98  --preprocessed_out                      false
% 2.71/0.98  --preprocessed_stats                    false
% 2.71/0.98  
% 2.71/0.98  ------ Abstraction refinement Options
% 2.71/0.98  
% 2.71/0.98  --abstr_ref                             []
% 2.71/0.98  --abstr_ref_prep                        false
% 2.71/0.98  --abstr_ref_until_sat                   false
% 2.71/0.98  --abstr_ref_sig_restrict                funpre
% 2.71/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.71/0.98  --abstr_ref_under                       []
% 2.71/0.98  
% 2.71/0.98  ------ SAT Options
% 2.71/0.98  
% 2.71/0.98  --sat_mode                              false
% 2.71/0.98  --sat_fm_restart_options                ""
% 2.71/0.98  --sat_gr_def                            false
% 2.71/0.98  --sat_epr_types                         true
% 2.71/0.98  --sat_non_cyclic_types                  false
% 2.71/0.98  --sat_finite_models                     false
% 2.71/0.98  --sat_fm_lemmas                         false
% 2.71/0.98  --sat_fm_prep                           false
% 2.71/0.98  --sat_fm_uc_incr                        true
% 2.71/0.98  --sat_out_model                         small
% 2.71/0.98  --sat_out_clauses                       false
% 2.71/0.98  
% 2.71/0.98  ------ QBF Options
% 2.71/0.98  
% 2.71/0.98  --qbf_mode                              false
% 2.71/0.98  --qbf_elim_univ                         false
% 2.71/0.98  --qbf_dom_inst                          none
% 2.71/0.98  --qbf_dom_pre_inst                      false
% 2.71/0.98  --qbf_sk_in                             false
% 2.71/0.98  --qbf_pred_elim                         true
% 2.71/0.98  --qbf_split                             512
% 2.71/0.98  
% 2.71/0.98  ------ BMC1 Options
% 2.71/0.98  
% 2.71/0.98  --bmc1_incremental                      false
% 2.71/0.98  --bmc1_axioms                           reachable_all
% 2.71/0.98  --bmc1_min_bound                        0
% 2.71/0.98  --bmc1_max_bound                        -1
% 2.71/0.98  --bmc1_max_bound_default                -1
% 2.71/0.98  --bmc1_symbol_reachability              true
% 2.71/0.98  --bmc1_property_lemmas                  false
% 2.71/0.98  --bmc1_k_induction                      false
% 2.71/0.98  --bmc1_non_equiv_states                 false
% 2.71/0.98  --bmc1_deadlock                         false
% 2.71/0.98  --bmc1_ucm                              false
% 2.71/0.98  --bmc1_add_unsat_core                   none
% 2.71/0.98  --bmc1_unsat_core_children              false
% 2.71/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.71/0.98  --bmc1_out_stat                         full
% 2.71/0.98  --bmc1_ground_init                      false
% 2.71/0.98  --bmc1_pre_inst_next_state              false
% 2.71/0.98  --bmc1_pre_inst_state                   false
% 2.71/0.98  --bmc1_pre_inst_reach_state             false
% 2.71/0.98  --bmc1_out_unsat_core                   false
% 2.71/0.98  --bmc1_aig_witness_out                  false
% 2.71/0.98  --bmc1_verbose                          false
% 2.71/0.98  --bmc1_dump_clauses_tptp                false
% 2.71/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.71/0.98  --bmc1_dump_file                        -
% 2.71/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.71/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.71/0.98  --bmc1_ucm_extend_mode                  1
% 2.71/0.98  --bmc1_ucm_init_mode                    2
% 2.71/0.98  --bmc1_ucm_cone_mode                    none
% 2.71/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.71/0.98  --bmc1_ucm_relax_model                  4
% 2.71/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.71/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.71/0.98  --bmc1_ucm_layered_model                none
% 2.71/0.98  --bmc1_ucm_max_lemma_size               10
% 2.71/0.98  
% 2.71/0.98  ------ AIG Options
% 2.71/0.98  
% 2.71/0.98  --aig_mode                              false
% 2.71/0.98  
% 2.71/0.98  ------ Instantiation Options
% 2.71/0.98  
% 2.71/0.98  --instantiation_flag                    true
% 2.71/0.98  --inst_sos_flag                         false
% 2.71/0.98  --inst_sos_phase                        true
% 2.71/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.71/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.71/0.98  --inst_lit_sel_side                     none
% 2.71/0.98  --inst_solver_per_active                1400
% 2.71/0.98  --inst_solver_calls_frac                1.
% 2.71/0.98  --inst_passive_queue_type               priority_queues
% 2.71/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.71/0.98  --inst_passive_queues_freq              [25;2]
% 2.71/0.98  --inst_dismatching                      true
% 2.71/0.98  --inst_eager_unprocessed_to_passive     true
% 2.71/0.98  --inst_prop_sim_given                   true
% 2.71/0.98  --inst_prop_sim_new                     false
% 2.71/0.98  --inst_subs_new                         false
% 2.71/0.98  --inst_eq_res_simp                      false
% 2.71/0.98  --inst_subs_given                       false
% 2.71/0.98  --inst_orphan_elimination               true
% 2.71/0.98  --inst_learning_loop_flag               true
% 2.71/0.98  --inst_learning_start                   3000
% 2.71/0.98  --inst_learning_factor                  2
% 2.71/0.98  --inst_start_prop_sim_after_learn       3
% 2.71/0.98  --inst_sel_renew                        solver
% 2.71/0.98  --inst_lit_activity_flag                true
% 2.71/0.98  --inst_restr_to_given                   false
% 2.71/0.98  --inst_activity_threshold               500
% 2.71/0.98  --inst_out_proof                        true
% 2.71/0.98  
% 2.71/0.98  ------ Resolution Options
% 2.71/0.98  
% 2.71/0.98  --resolution_flag                       false
% 2.71/0.98  --res_lit_sel                           adaptive
% 2.71/0.98  --res_lit_sel_side                      none
% 2.71/0.98  --res_ordering                          kbo
% 2.71/0.98  --res_to_prop_solver                    active
% 2.71/0.98  --res_prop_simpl_new                    false
% 2.71/0.98  --res_prop_simpl_given                  true
% 2.71/0.98  --res_passive_queue_type                priority_queues
% 2.71/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.71/0.98  --res_passive_queues_freq               [15;5]
% 2.71/0.98  --res_forward_subs                      full
% 2.71/0.98  --res_backward_subs                     full
% 2.71/0.98  --res_forward_subs_resolution           true
% 2.71/0.98  --res_backward_subs_resolution          true
% 2.71/0.98  --res_orphan_elimination                true
% 2.71/0.98  --res_time_limit                        2.
% 2.71/0.98  --res_out_proof                         true
% 2.71/0.98  
% 2.71/0.98  ------ Superposition Options
% 2.71/0.98  
% 2.71/0.98  --superposition_flag                    true
% 2.71/0.98  --sup_passive_queue_type                priority_queues
% 2.71/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.71/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.71/0.98  --demod_completeness_check              fast
% 2.71/0.98  --demod_use_ground                      true
% 2.71/0.98  --sup_to_prop_solver                    passive
% 2.71/0.98  --sup_prop_simpl_new                    true
% 2.71/0.98  --sup_prop_simpl_given                  true
% 2.71/0.98  --sup_fun_splitting                     false
% 2.71/0.98  --sup_smt_interval                      50000
% 2.71/0.98  
% 2.71/0.98  ------ Superposition Simplification Setup
% 2.71/0.98  
% 2.71/0.98  --sup_indices_passive                   []
% 2.71/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.71/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.71/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.71/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.71/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.71/0.98  --sup_full_bw                           [BwDemod]
% 2.71/0.98  --sup_immed_triv                        [TrivRules]
% 2.71/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.71/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.71/0.98  --sup_immed_bw_main                     []
% 2.71/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.71/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.71/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.71/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.71/0.98  
% 2.71/0.98  ------ Combination Options
% 2.71/0.98  
% 2.71/0.98  --comb_res_mult                         3
% 2.71/0.98  --comb_sup_mult                         2
% 2.71/0.98  --comb_inst_mult                        10
% 2.71/0.98  
% 2.71/0.98  ------ Debug Options
% 2.71/0.98  
% 2.71/0.98  --dbg_backtrace                         false
% 2.71/0.98  --dbg_dump_prop_clauses                 false
% 2.71/0.98  --dbg_dump_prop_clauses_file            -
% 2.71/0.98  --dbg_out_stat                          false
% 2.71/0.98  
% 2.71/0.98  
% 2.71/0.98  
% 2.71/0.98  
% 2.71/0.98  ------ Proving...
% 2.71/0.98  
% 2.71/0.98  
% 2.71/0.98  % SZS status Theorem for theBenchmark.p
% 2.71/0.98  
% 2.71/0.98   Resolution empty clause
% 2.71/0.98  
% 2.71/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.71/0.98  
% 2.71/0.98  fof(f19,axiom,(
% 2.71/0.98    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5,X6] : ((r2_hidden(X6,X1) & r2_hidden(X5,X6) & r2_hidden(X4,X5) & r2_hidden(X3,X4) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 2.71/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/0.98  
% 2.71/0.98  fof(f24,plain,(
% 2.71/0.98    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.71/0.98    inference(pure_predicate_removal,[],[f19])).
% 2.71/0.98  
% 2.71/0.98  fof(f35,plain,(
% 2.71/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.71/0.98    inference(ennf_transformation,[],[f24])).
% 2.71/0.98  
% 2.71/0.98  fof(f46,plain,(
% 2.71/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 2.71/0.98    introduced(choice_axiom,[])).
% 2.71/0.98  
% 2.71/0.98  fof(f47,plain,(
% 2.71/0.98    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 2.71/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f46])).
% 2.71/0.98  
% 2.71/0.98  fof(f74,plain,(
% 2.71/0.98    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 2.71/0.98    inference(cnf_transformation,[],[f47])).
% 2.71/0.98  
% 2.71/0.98  fof(f11,axiom,(
% 2.71/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.71/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/0.98  
% 2.71/0.98  fof(f27,plain,(
% 2.71/0.98    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.71/0.98    inference(ennf_transformation,[],[f11])).
% 2.71/0.98  
% 2.71/0.98  fof(f63,plain,(
% 2.71/0.98    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.71/0.98    inference(cnf_transformation,[],[f27])).
% 2.71/0.98  
% 2.71/0.98  fof(f22,conjecture,(
% 2.71/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 2.71/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/0.98  
% 2.71/0.98  fof(f23,negated_conjecture,(
% 2.71/0.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 2.71/0.98    inference(negated_conjecture,[],[f22])).
% 2.71/0.98  
% 2.71/0.98  fof(f39,plain,(
% 2.71/0.98    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 2.71/0.98    inference(ennf_transformation,[],[f23])).
% 2.71/0.98  
% 2.71/0.98  fof(f40,plain,(
% 2.71/0.98    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 2.71/0.98    inference(flattening,[],[f39])).
% 2.71/0.98  
% 2.71/0.98  fof(f49,plain,(
% 2.71/0.98    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (~r2_hidden(k1_funct_1(sK4,sK2),sK3) & k1_xboole_0 != sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) & v1_funct_2(sK4,k1_tarski(sK2),sK3) & v1_funct_1(sK4))),
% 2.71/0.98    introduced(choice_axiom,[])).
% 2.71/0.98  
% 2.71/0.98  fof(f50,plain,(
% 2.71/0.98    ~r2_hidden(k1_funct_1(sK4,sK2),sK3) & k1_xboole_0 != sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) & v1_funct_2(sK4,k1_tarski(sK2),sK3) & v1_funct_1(sK4)),
% 2.71/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f40,f49])).
% 2.71/0.98  
% 2.71/0.98  fof(f85,plain,(
% 2.71/0.98    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))),
% 2.71/0.98    inference(cnf_transformation,[],[f50])).
% 2.71/0.98  
% 2.71/0.98  fof(f3,axiom,(
% 2.71/0.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.71/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/0.98  
% 2.71/0.98  fof(f55,plain,(
% 2.71/0.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.71/0.98    inference(cnf_transformation,[],[f3])).
% 2.71/0.98  
% 2.71/0.98  fof(f4,axiom,(
% 2.71/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.71/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/0.98  
% 2.71/0.98  fof(f56,plain,(
% 2.71/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.71/0.98    inference(cnf_transformation,[],[f4])).
% 2.71/0.98  
% 2.71/0.98  fof(f5,axiom,(
% 2.71/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.71/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/0.98  
% 2.71/0.98  fof(f57,plain,(
% 2.71/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.71/0.98    inference(cnf_transformation,[],[f5])).
% 2.71/0.98  
% 2.71/0.98  fof(f6,axiom,(
% 2.71/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.71/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/0.98  
% 2.71/0.98  fof(f58,plain,(
% 2.71/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.71/0.98    inference(cnf_transformation,[],[f6])).
% 2.71/0.98  
% 2.71/0.98  fof(f7,axiom,(
% 2.71/0.98    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.71/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/0.98  
% 2.71/0.98  fof(f59,plain,(
% 2.71/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.71/0.98    inference(cnf_transformation,[],[f7])).
% 2.71/0.98  
% 2.71/0.98  fof(f8,axiom,(
% 2.71/0.98    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.71/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/0.98  
% 2.71/0.98  fof(f60,plain,(
% 2.71/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.71/0.98    inference(cnf_transformation,[],[f8])).
% 2.71/0.98  
% 2.71/0.98  fof(f9,axiom,(
% 2.71/0.98    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 2.71/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/0.98  
% 2.71/0.98  fof(f61,plain,(
% 2.71/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 2.71/0.98    inference(cnf_transformation,[],[f9])).
% 2.71/0.98  
% 2.71/0.98  fof(f88,plain,(
% 2.71/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.71/0.98    inference(definition_unfolding,[],[f60,f61])).
% 2.71/0.98  
% 2.71/0.98  fof(f89,plain,(
% 2.71/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.71/0.98    inference(definition_unfolding,[],[f59,f88])).
% 2.71/0.98  
% 2.71/0.98  fof(f90,plain,(
% 2.71/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.71/0.98    inference(definition_unfolding,[],[f58,f89])).
% 2.71/0.98  
% 2.71/0.98  fof(f91,plain,(
% 2.71/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.71/0.98    inference(definition_unfolding,[],[f57,f90])).
% 2.71/0.98  
% 2.71/0.98  fof(f92,plain,(
% 2.71/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.71/0.98    inference(definition_unfolding,[],[f56,f91])).
% 2.71/0.98  
% 2.71/0.98  fof(f93,plain,(
% 2.71/0.98    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.71/0.98    inference(definition_unfolding,[],[f55,f92])).
% 2.71/0.98  
% 2.71/0.98  fof(f97,plain,(
% 2.71/0.98    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))),
% 2.71/0.98    inference(definition_unfolding,[],[f85,f93])).
% 2.71/0.98  
% 2.71/0.98  fof(f84,plain,(
% 2.71/0.98    v1_funct_2(sK4,k1_tarski(sK2),sK3)),
% 2.71/0.98    inference(cnf_transformation,[],[f50])).
% 2.71/0.98  
% 2.71/0.98  fof(f98,plain,(
% 2.71/0.98    v1_funct_2(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)),
% 2.71/0.98    inference(definition_unfolding,[],[f84,f93])).
% 2.71/0.98  
% 2.71/0.98  fof(f21,axiom,(
% 2.71/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.71/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/0.98  
% 2.71/0.98  fof(f37,plain,(
% 2.71/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.71/0.98    inference(ennf_transformation,[],[f21])).
% 2.71/0.98  
% 2.71/0.98  fof(f38,plain,(
% 2.71/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.71/0.98    inference(flattening,[],[f37])).
% 2.71/0.98  
% 2.71/0.98  fof(f48,plain,(
% 2.71/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.71/0.98    inference(nnf_transformation,[],[f38])).
% 2.71/0.98  
% 2.71/0.98  fof(f77,plain,(
% 2.71/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.71/0.98    inference(cnf_transformation,[],[f48])).
% 2.71/0.98  
% 2.71/0.98  fof(f86,plain,(
% 2.71/0.98    k1_xboole_0 != sK3),
% 2.71/0.98    inference(cnf_transformation,[],[f50])).
% 2.71/0.98  
% 2.71/0.98  fof(f17,axiom,(
% 2.71/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.71/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/0.98  
% 2.71/0.98  fof(f33,plain,(
% 2.71/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.71/0.98    inference(ennf_transformation,[],[f17])).
% 2.71/0.98  
% 2.71/0.98  fof(f71,plain,(
% 2.71/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.71/0.98    inference(cnf_transformation,[],[f33])).
% 2.71/0.98  
% 2.71/0.98  fof(f18,axiom,(
% 2.71/0.98    ! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) => (r2_hidden(k2_mcart_1(X0),X3) & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 2.71/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/0.98  
% 2.71/0.98  fof(f34,plain,(
% 2.71/0.98    ! [X0,X1,X2,X3] : ((r2_hidden(k2_mcart_1(X0),X3) & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)) | ~r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)))),
% 2.71/0.98    inference(ennf_transformation,[],[f18])).
% 2.71/0.98  
% 2.71/0.98  fof(f72,plain,(
% 2.71/0.98    ( ! [X2,X0,X3,X1] : (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1 | ~r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3))) )),
% 2.71/0.98    inference(cnf_transformation,[],[f34])).
% 2.71/0.98  
% 2.71/0.98  fof(f96,plain,(
% 2.71/0.98    ( ! [X2,X0,X3,X1] : (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1 | ~r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),X3))) )),
% 2.71/0.98    inference(definition_unfolding,[],[f72,f92])).
% 2.71/0.98  
% 2.71/0.98  fof(f20,axiom,(
% 2.71/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r2_hidden(X1,X0) => (r2_hidden(k2_mcart_1(X1),k2_relat_1(X0)) & r2_hidden(k1_mcart_1(X1),k1_relat_1(X0)))))),
% 2.71/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/0.98  
% 2.71/0.98  fof(f36,plain,(
% 2.71/0.98    ! [X0] : (! [X1] : ((r2_hidden(k2_mcart_1(X1),k2_relat_1(X0)) & r2_hidden(k1_mcart_1(X1),k1_relat_1(X0))) | ~r2_hidden(X1,X0)) | ~v1_relat_1(X0))),
% 2.71/0.98    inference(ennf_transformation,[],[f20])).
% 2.71/0.98  
% 2.71/0.98  fof(f75,plain,(
% 2.71/0.98    ( ! [X0,X1] : (r2_hidden(k1_mcart_1(X1),k1_relat_1(X0)) | ~r2_hidden(X1,X0) | ~v1_relat_1(X0)) )),
% 2.71/0.98    inference(cnf_transformation,[],[f36])).
% 2.71/0.98  
% 2.71/0.98  fof(f15,axiom,(
% 2.71/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.71/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/0.98  
% 2.71/0.98  fof(f31,plain,(
% 2.71/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.71/0.98    inference(ennf_transformation,[],[f15])).
% 2.71/0.98  
% 2.71/0.98  fof(f69,plain,(
% 2.71/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.71/0.98    inference(cnf_transformation,[],[f31])).
% 2.71/0.98  
% 2.71/0.98  fof(f76,plain,(
% 2.71/0.98    ( ! [X0,X1] : (r2_hidden(k2_mcart_1(X1),k2_relat_1(X0)) | ~r2_hidden(X1,X0) | ~v1_relat_1(X0)) )),
% 2.71/0.98    inference(cnf_transformation,[],[f36])).
% 2.71/0.98  
% 2.71/0.98  fof(f16,axiom,(
% 2.71/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.71/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/0.98  
% 2.71/0.98  fof(f25,plain,(
% 2.71/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.71/0.98    inference(pure_predicate_removal,[],[f16])).
% 2.71/0.98  
% 2.71/0.98  fof(f32,plain,(
% 2.71/0.98    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.71/0.98    inference(ennf_transformation,[],[f25])).
% 2.71/0.98  
% 2.71/0.98  fof(f70,plain,(
% 2.71/0.98    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.71/0.98    inference(cnf_transformation,[],[f32])).
% 2.71/0.98  
% 2.71/0.98  fof(f12,axiom,(
% 2.71/0.98    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.71/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/0.98  
% 2.71/0.98  fof(f28,plain,(
% 2.71/0.98    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.71/0.98    inference(ennf_transformation,[],[f12])).
% 2.71/0.98  
% 2.71/0.98  fof(f45,plain,(
% 2.71/0.98    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.71/0.98    inference(nnf_transformation,[],[f28])).
% 2.71/0.98  
% 2.71/0.98  fof(f64,plain,(
% 2.71/0.98    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.71/0.98    inference(cnf_transformation,[],[f45])).
% 2.71/0.98  
% 2.71/0.98  fof(f14,axiom,(
% 2.71/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 2.71/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/0.98  
% 2.71/0.98  fof(f29,plain,(
% 2.71/0.98    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.71/0.98    inference(ennf_transformation,[],[f14])).
% 2.71/0.98  
% 2.71/0.98  fof(f30,plain,(
% 2.71/0.98    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.71/0.98    inference(flattening,[],[f29])).
% 2.71/0.98  
% 2.71/0.98  fof(f68,plain,(
% 2.71/0.98    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.71/0.98    inference(cnf_transformation,[],[f30])).
% 2.71/0.98  
% 2.71/0.98  fof(f83,plain,(
% 2.71/0.98    v1_funct_1(sK4)),
% 2.71/0.98    inference(cnf_transformation,[],[f50])).
% 2.71/0.98  
% 2.71/0.98  fof(f1,axiom,(
% 2.71/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.71/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/0.98  
% 2.71/0.98  fof(f26,plain,(
% 2.71/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.71/0.98    inference(ennf_transformation,[],[f1])).
% 2.71/0.98  
% 2.71/0.98  fof(f41,plain,(
% 2.71/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.71/0.98    inference(nnf_transformation,[],[f26])).
% 2.71/0.98  
% 2.71/0.98  fof(f42,plain,(
% 2.71/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.71/0.98    inference(rectify,[],[f41])).
% 2.71/0.98  
% 2.71/0.98  fof(f43,plain,(
% 2.71/0.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.71/0.98    introduced(choice_axiom,[])).
% 2.71/0.98  
% 2.71/0.98  fof(f44,plain,(
% 2.71/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.71/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).
% 2.71/0.98  
% 2.71/0.98  fof(f51,plain,(
% 2.71/0.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.71/0.98    inference(cnf_transformation,[],[f44])).
% 2.71/0.98  
% 2.71/0.98  fof(f87,plain,(
% 2.71/0.98    ~r2_hidden(k1_funct_1(sK4,sK2),sK3)),
% 2.71/0.98    inference(cnf_transformation,[],[f50])).
% 2.71/0.98  
% 2.71/0.98  fof(f2,axiom,(
% 2.71/0.98    v1_xboole_0(k1_xboole_0)),
% 2.71/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/0.98  
% 2.71/0.98  fof(f54,plain,(
% 2.71/0.98    v1_xboole_0(k1_xboole_0)),
% 2.71/0.98    inference(cnf_transformation,[],[f2])).
% 2.71/0.98  
% 2.71/0.98  fof(f10,axiom,(
% 2.71/0.98    ! [X0,X1,X2,X3,X4] : ~v1_xboole_0(k3_enumset1(X0,X1,X2,X3,X4))),
% 2.71/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/0.98  
% 2.71/0.98  fof(f62,plain,(
% 2.71/0.98    ( ! [X4,X2,X0,X3,X1] : (~v1_xboole_0(k3_enumset1(X0,X1,X2,X3,X4))) )),
% 2.71/0.98    inference(cnf_transformation,[],[f10])).
% 2.71/0.98  
% 2.71/0.98  fof(f94,plain,(
% 2.71/0.98    ( ! [X4,X2,X0,X3,X1] : (~v1_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4))) )),
% 2.71/0.98    inference(definition_unfolding,[],[f62,f89])).
% 2.71/0.98  
% 2.71/0.98  fof(f13,axiom,(
% 2.71/0.98    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.71/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/0.98  
% 2.71/0.98  fof(f66,plain,(
% 2.71/0.98    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.71/0.98    inference(cnf_transformation,[],[f13])).
% 2.71/0.98  
% 2.71/0.98  cnf(c_16,plain,
% 2.71/0.98      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 2.71/0.98      inference(cnf_transformation,[],[f74]) ).
% 2.71/0.98  
% 2.71/0.98  cnf(c_1264,plain,
% 2.71/0.98      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 2.71/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.71/0.98  
% 2.71/0.98  cnf(c_5,plain,
% 2.71/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.71/0.98      | ~ r2_hidden(X2,X0)
% 2.71/0.98      | r2_hidden(X2,X1) ),
% 2.71/0.98      inference(cnf_transformation,[],[f63]) ).
% 2.71/0.98  
% 2.71/0.98  cnf(c_27,negated_conjecture,
% 2.71/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) ),
% 2.71/0.98      inference(cnf_transformation,[],[f97]) ).
% 2.71/0.98  
% 2.71/0.98  cnf(c_459,plain,
% 2.71/0.98      ( ~ r2_hidden(X0,X1)
% 2.71/0.98      | r2_hidden(X0,X2)
% 2.71/0.98      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(X2)
% 2.71/0.98      | sK4 != X1 ),
% 2.71/0.98      inference(resolution_lifted,[status(thm)],[c_5,c_27]) ).
% 2.71/0.98  
% 2.71/0.98  cnf(c_460,plain,
% 2.71/0.98      ( r2_hidden(X0,X1)
% 2.71/0.98      | ~ r2_hidden(X0,sK4)
% 2.71/0.98      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(X1) ),
% 2.71/0.98      inference(unflattening,[status(thm)],[c_459]) ).
% 2.71/0.98  
% 2.71/0.98  cnf(c_1262,plain,
% 2.71/0.98      ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(X0)
% 2.71/0.98      | r2_hidden(X1,X0) = iProver_top
% 2.71/0.98      | r2_hidden(X1,sK4) != iProver_top ),
% 2.71/0.98      inference(predicate_to_equality,[status(thm)],[c_460]) ).
% 2.71/0.98  
% 2.71/0.98  cnf(c_28,negated_conjecture,
% 2.71/0.98      ( v1_funct_2(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) ),
% 2.71/0.98      inference(cnf_transformation,[],[f98]) ).
% 2.71/0.98  
% 2.71/0.98  cnf(c_24,plain,
% 2.71/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.71/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.71/0.98      | k1_relset_1(X1,X2,X0) = X1
% 2.71/0.98      | k1_xboole_0 = X2 ),
% 2.71/0.98      inference(cnf_transformation,[],[f77]) ).
% 2.71/0.98  
% 2.71/0.98  cnf(c_486,plain,
% 2.71/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.71/0.98      | k1_relset_1(X1,X2,X0) = X1
% 2.71/0.98      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 2.71/0.98      | sK4 != X0
% 2.71/0.98      | k1_xboole_0 = X2 ),
% 2.71/0.98      inference(resolution_lifted,[status(thm)],[c_24,c_27]) ).
% 2.71/0.98  
% 2.71/0.98  cnf(c_487,plain,
% 2.71/0.98      ( ~ v1_funct_2(sK4,X0,X1)
% 2.71/0.98      | k1_relset_1(X0,X1,sK4) = X0
% 2.71/0.98      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.71/0.98      | k1_xboole_0 = X1 ),
% 2.71/0.98      inference(unflattening,[status(thm)],[c_486]) ).
% 2.71/0.98  
% 2.71/0.98  cnf(c_762,plain,
% 2.71/0.98      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != X0
% 2.71/0.98      | k1_relset_1(X0,X1,sK4) = X0
% 2.71/0.98      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.71/0.98      | sK3 != X1
% 2.71/0.98      | sK4 != sK4
% 2.71/0.98      | k1_xboole_0 = X1 ),
% 2.71/0.98      inference(resolution_lifted,[status(thm)],[c_28,c_487]) ).
% 2.71/0.98  
% 2.71/0.98  cnf(c_763,plain,
% 2.71/0.98      ( k1_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 2.71/0.98      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))
% 2.71/0.98      | k1_xboole_0 = sK3 ),
% 2.71/0.98      inference(unflattening,[status(thm)],[c_762]) ).
% 2.71/0.98  
% 2.71/0.98  cnf(c_26,negated_conjecture,
% 2.71/0.98      ( k1_xboole_0 != sK3 ),
% 2.71/0.98      inference(cnf_transformation,[],[f86]) ).
% 2.71/0.98  
% 2.71/0.98  cnf(c_764,plain,
% 2.71/0.98      ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))
% 2.71/0.98      | k1_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 2.71/0.98      inference(global_propositional_subsumption,[status(thm)],[c_763,c_26]) ).
% 2.71/0.98  
% 2.71/0.98  cnf(c_765,plain,
% 2.71/0.98      ( k1_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 2.71/0.98      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) ),
% 2.71/0.98      inference(renaming,[status(thm)],[c_764]) ).
% 2.71/0.98  
% 2.71/0.98  cnf(c_814,plain,
% 2.71/0.98      ( k1_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 2.71/0.98      inference(equality_resolution_simp,[status(thm)],[c_765]) ).
% 2.71/0.98  
% 2.71/0.98  cnf(c_13,plain,
% 2.71/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.71/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.71/0.98      inference(cnf_transformation,[],[f71]) ).
% 2.71/0.98  
% 2.71/0.98  cnf(c_522,plain,
% 2.71/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.71/0.98      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.71/0.98      | sK4 != X2 ),
% 2.71/0.98      inference(resolution_lifted,[status(thm)],[c_13,c_27]) ).
% 2.71/0.98  
% 2.71/0.98  cnf(c_523,plain,
% 2.71/0.98      ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
% 2.71/0.98      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.71/0.98      inference(unflattening,[status(thm)],[c_522]) ).
% 2.71/0.98  
% 2.71/0.98  cnf(c_1416,plain,
% 2.71/0.98      ( k1_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4) = k1_relat_1(sK4) ),
% 2.71/0.98      inference(equality_resolution,[status(thm)],[c_523]) ).
% 2.71/0.98  
% 2.71/0.98  cnf(c_1429,plain,
% 2.71/0.98      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_relat_1(sK4) ),
% 2.71/0.99      inference(light_normalisation,[status(thm)],[c_814,c_1416]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_1646,plain,
% 2.71/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3)) != k1_zfmisc_1(X0)
% 2.71/0.99      | r2_hidden(X1,X0) = iProver_top
% 2.71/0.99      | r2_hidden(X1,sK4) != iProver_top ),
% 2.71/0.99      inference(light_normalisation,[status(thm)],[c_1262,c_1429]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_1653,plain,
% 2.71/0.99      ( r2_hidden(X0,k2_zfmisc_1(k1_relat_1(sK4),sK3)) = iProver_top
% 2.71/0.99      | r2_hidden(X0,sK4) != iProver_top ),
% 2.71/0.99      inference(equality_resolution,[status(thm)],[c_1646]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_15,plain,
% 2.71/0.99      ( ~ r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),X3))
% 2.71/0.99      | k1_mcart_1(X0) = X2
% 2.71/0.99      | k1_mcart_1(X0) = X1 ),
% 2.71/0.99      inference(cnf_transformation,[],[f96]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_1265,plain,
% 2.71/0.99      ( k1_mcart_1(X0) = X1
% 2.71/0.99      | k1_mcart_1(X0) = X2
% 2.71/0.99      | r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),X3)) != iProver_top ),
% 2.71/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_2036,plain,
% 2.71/0.99      ( k1_mcart_1(X0) = sK2
% 2.71/0.99      | r2_hidden(X0,k2_zfmisc_1(k1_relat_1(sK4),X1)) != iProver_top ),
% 2.71/0.99      inference(superposition,[status(thm)],[c_1429,c_1265]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_2767,plain,
% 2.71/0.99      ( k1_mcart_1(X0) = sK2 | r2_hidden(X0,sK4) != iProver_top ),
% 2.71/0.99      inference(superposition,[status(thm)],[c_1653,c_2036]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_3549,plain,
% 2.71/0.99      ( k1_mcart_1(sK1(sK4)) = sK2 | sK4 = k1_xboole_0 ),
% 2.71/0.99      inference(superposition,[status(thm)],[c_1264,c_2767]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_18,plain,
% 2.71/0.99      ( ~ r2_hidden(X0,X1)
% 2.71/0.99      | r2_hidden(k1_mcart_1(X0),k1_relat_1(X1))
% 2.71/0.99      | ~ v1_relat_1(X1) ),
% 2.71/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_11,plain,
% 2.71/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.71/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_531,plain,
% 2.71/0.99      ( v1_relat_1(X0)
% 2.71/0.99      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 2.71/0.99      | sK4 != X0 ),
% 2.71/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_27]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_532,plain,
% 2.71/0.99      ( v1_relat_1(sK4)
% 2.71/0.99      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.71/0.99      inference(unflattening,[status(thm)],[c_531]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_712,plain,
% 2.71/0.99      ( ~ r2_hidden(X0,X1)
% 2.71/0.99      | r2_hidden(k1_mcart_1(X0),k1_relat_1(X1))
% 2.71/0.99      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
% 2.71/0.99      | sK4 != X1 ),
% 2.71/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_532]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_713,plain,
% 2.71/0.99      ( ~ r2_hidden(X0,sK4)
% 2.71/0.99      | r2_hidden(k1_mcart_1(X0),k1_relat_1(sK4))
% 2.71/0.99      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
% 2.71/0.99      inference(unflattening,[status(thm)],[c_712]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_943,plain,
% 2.71/0.99      ( ~ r2_hidden(X0,sK4)
% 2.71/0.99      | r2_hidden(k1_mcart_1(X0),k1_relat_1(sK4))
% 2.71/0.99      | ~ sP2_iProver_split ),
% 2.71/0.99      inference(splitting,
% 2.71/0.99                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 2.71/0.99                [c_713]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_1256,plain,
% 2.71/0.99      ( r2_hidden(X0,sK4) != iProver_top
% 2.71/0.99      | r2_hidden(k1_mcart_1(X0),k1_relat_1(sK4)) = iProver_top
% 2.71/0.99      | sP2_iProver_split != iProver_top ),
% 2.71/0.99      inference(predicate_to_equality,[status(thm)],[c_943]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_944,plain,
% 2.71/0.99      ( sP2_iProver_split | sP0_iProver_split ),
% 2.71/0.99      inference(splitting,
% 2.71/0.99                [splitting(split),new_symbols(definition,[])],
% 2.71/0.99                [c_713]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_977,plain,
% 2.71/0.99      ( sP2_iProver_split = iProver_top | sP0_iProver_split = iProver_top ),
% 2.71/0.99      inference(predicate_to_equality,[status(thm)],[c_944]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_978,plain,
% 2.71/0.99      ( r2_hidden(X0,sK4) != iProver_top
% 2.71/0.99      | r2_hidden(k1_mcart_1(X0),k1_relat_1(sK4)) = iProver_top
% 2.71/0.99      | sP2_iProver_split != iProver_top ),
% 2.71/0.99      inference(predicate_to_equality,[status(thm)],[c_943]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_948,plain,( X0 = X0 ),theory(equality) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_1403,plain,
% 2.71/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) ),
% 2.71/0.99      inference(instantiation,[status(thm)],[c_948]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_17,plain,
% 2.71/0.99      ( ~ r2_hidden(X0,X1)
% 2.71/0.99      | r2_hidden(k2_mcart_1(X0),k2_relat_1(X1))
% 2.71/0.99      | ~ v1_relat_1(X1) ),
% 2.71/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_727,plain,
% 2.71/0.99      ( ~ r2_hidden(X0,X1)
% 2.71/0.99      | r2_hidden(k2_mcart_1(X0),k2_relat_1(X1))
% 2.71/0.99      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
% 2.71/0.99      | sK4 != X1 ),
% 2.71/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_532]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_728,plain,
% 2.71/0.99      ( ~ r2_hidden(X0,sK4)
% 2.71/0.99      | r2_hidden(k2_mcart_1(X0),k2_relat_1(sK4))
% 2.71/0.99      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
% 2.71/0.99      inference(unflattening,[status(thm)],[c_727]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_940,plain,
% 2.71/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.71/0.99      | ~ sP0_iProver_split ),
% 2.71/0.99      inference(splitting,
% 2.71/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.71/0.99                [c_728]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_1460,plain,
% 2.71/0.99      ( ~ sP0_iProver_split
% 2.71/0.99      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) ),
% 2.71/0.99      inference(instantiation,[status(thm)],[c_940]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_1462,plain,
% 2.71/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))
% 2.71/0.99      | sP0_iProver_split != iProver_top ),
% 2.71/0.99      inference(predicate_to_equality,[status(thm)],[c_1460]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_1836,plain,
% 2.71/0.99      ( r2_hidden(k1_mcart_1(X0),k1_relat_1(sK4)) = iProver_top
% 2.71/0.99      | r2_hidden(X0,sK4) != iProver_top ),
% 2.71/0.99      inference(global_propositional_subsumption,
% 2.71/0.99                [status(thm)],
% 2.71/0.99                [c_1256,c_977,c_978,c_1403,c_1462]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_1837,plain,
% 2.71/0.99      ( r2_hidden(X0,sK4) != iProver_top
% 2.71/0.99      | r2_hidden(k1_mcart_1(X0),k1_relat_1(sK4)) = iProver_top ),
% 2.71/0.99      inference(renaming,[status(thm)],[c_1836]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_3856,plain,
% 2.71/0.99      ( sK4 = k1_xboole_0
% 2.71/0.99      | r2_hidden(sK1(sK4),sK4) != iProver_top
% 2.71/0.99      | r2_hidden(sK2,k1_relat_1(sK4)) = iProver_top ),
% 2.71/0.99      inference(superposition,[status(thm)],[c_3549,c_1837]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_12,plain,
% 2.71/0.99      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.71/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_7,plain,
% 2.71/0.99      ( ~ v5_relat_1(X0,X1) | r1_tarski(k2_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 2.71/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_334,plain,
% 2.71/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.71/0.99      | r1_tarski(k2_relat_1(X0),X2)
% 2.71/0.99      | ~ v1_relat_1(X0) ),
% 2.71/0.99      inference(resolution,[status(thm)],[c_12,c_7]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_338,plain,
% 2.71/0.99      ( r1_tarski(k2_relat_1(X0),X2)
% 2.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.71/0.99      inference(global_propositional_subsumption,[status(thm)],[c_334,c_11]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_339,plain,
% 2.71/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.71/0.99      | r1_tarski(k2_relat_1(X0),X2) ),
% 2.71/0.99      inference(renaming,[status(thm)],[c_338]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_474,plain,
% 2.71/0.99      ( r1_tarski(k2_relat_1(X0),X1)
% 2.71/0.99      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X2,X1))
% 2.71/0.99      | sK4 != X0 ),
% 2.71/0.99      inference(resolution_lifted,[status(thm)],[c_339,c_27]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_475,plain,
% 2.71/0.99      ( r1_tarski(k2_relat_1(sK4),X0)
% 2.71/0.99      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X1,X0)) ),
% 2.71/0.99      inference(unflattening,[status(thm)],[c_474]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_1404,plain,
% 2.71/0.99      ( r1_tarski(k2_relat_1(sK4),sK3)
% 2.71/0.99      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) ),
% 2.71/0.99      inference(instantiation,[status(thm)],[c_475]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_1405,plain,
% 2.71/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))
% 2.71/0.99      | r1_tarski(k2_relat_1(sK4),sK3) = iProver_top ),
% 2.71/0.99      inference(predicate_to_equality,[status(thm)],[c_1404]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_10,plain,
% 2.71/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.71/0.99      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 2.71/0.99      | ~ v1_funct_1(X1)
% 2.71/0.99      | ~ v1_relat_1(X1) ),
% 2.71/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_29,negated_conjecture,
% 2.71/0.99      ( v1_funct_1(sK4) ),
% 2.71/0.99      inference(cnf_transformation,[],[f83]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_315,plain,
% 2.71/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.71/0.99      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 2.71/0.99      | ~ v1_relat_1(X1)
% 2.71/0.99      | sK4 != X1 ),
% 2.71/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_29]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_316,plain,
% 2.71/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 2.71/0.99      | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4))
% 2.71/0.99      | ~ v1_relat_1(sK4) ),
% 2.71/0.99      inference(unflattening,[status(thm)],[c_315]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_698,plain,
% 2.71/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 2.71/0.99      | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4))
% 2.71/0.99      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
% 2.71/0.99      inference(resolution,[status(thm)],[c_532,c_316]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_945,plain,
% 2.71/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 2.71/0.99      | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4))
% 2.71/0.99      | ~ sP3_iProver_split ),
% 2.71/0.99      inference(splitting,
% 2.71/0.99                [splitting(split),new_symbols(definition,[sP3_iProver_split])],
% 2.71/0.99                [c_698]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_1259,plain,
% 2.71/0.99      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.71/0.99      | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top
% 2.71/0.99      | sP3_iProver_split != iProver_top ),
% 2.71/0.99      inference(predicate_to_equality,[status(thm)],[c_945]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_946,plain,
% 2.71/0.99      ( sP3_iProver_split | sP0_iProver_split ),
% 2.71/0.99      inference(splitting,
% 2.71/0.99                [splitting(split),new_symbols(definition,[])],
% 2.71/0.99                [c_698]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_982,plain,
% 2.71/0.99      ( sP3_iProver_split = iProver_top | sP0_iProver_split = iProver_top ),
% 2.71/0.99      inference(predicate_to_equality,[status(thm)],[c_946]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_983,plain,
% 2.71/0.99      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.71/0.99      | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top
% 2.71/0.99      | sP3_iProver_split != iProver_top ),
% 2.71/0.99      inference(predicate_to_equality,[status(thm)],[c_945]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_1937,plain,
% 2.71/0.99      ( r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top
% 2.71/0.99      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
% 2.71/0.99      inference(global_propositional_subsumption,
% 2.71/0.99                [status(thm)],
% 2.71/0.99                [c_1259,c_982,c_983,c_1403,c_1462]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_1938,plain,
% 2.71/0.99      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.71/0.99      | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top ),
% 2.71/0.99      inference(renaming,[status(thm)],[c_1937]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_2,plain,
% 2.71/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 2.71/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_1267,plain,
% 2.71/0.99      ( r2_hidden(X0,X1) != iProver_top
% 2.71/0.99      | r2_hidden(X0,X2) = iProver_top
% 2.71/0.99      | r1_tarski(X1,X2) != iProver_top ),
% 2.71/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_2131,plain,
% 2.71/0.99      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.71/0.99      | r2_hidden(k1_funct_1(sK4,X0),X1) = iProver_top
% 2.71/0.99      | r1_tarski(k2_relat_1(sK4),X1) != iProver_top ),
% 2.71/0.99      inference(superposition,[status(thm)],[c_1938,c_1267]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_25,negated_conjecture,
% 2.71/0.99      ( ~ r2_hidden(k1_funct_1(sK4,sK2),sK3) ),
% 2.71/0.99      inference(cnf_transformation,[],[f87]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_1263,plain,
% 2.71/0.99      ( r2_hidden(k1_funct_1(sK4,sK2),sK3) != iProver_top ),
% 2.71/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_3289,plain,
% 2.71/0.99      ( r2_hidden(sK2,k1_relat_1(sK4)) != iProver_top
% 2.71/0.99      | r1_tarski(k2_relat_1(sK4),sK3) != iProver_top ),
% 2.71/0.99      inference(superposition,[status(thm)],[c_2131,c_1263]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_4028,plain,
% 2.71/0.99      ( r2_hidden(sK1(sK4),sK4) != iProver_top | sK4 = k1_xboole_0 ),
% 2.71/0.99      inference(global_propositional_subsumption,
% 2.71/0.99                [status(thm)],
% 2.71/0.99                [c_3856,c_1403,c_1405,c_3289]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_4029,plain,
% 2.71/0.99      ( sK4 = k1_xboole_0 | r2_hidden(sK1(sK4),sK4) != iProver_top ),
% 2.71/0.99      inference(renaming,[status(thm)],[c_4028]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_4034,plain,
% 2.71/0.99      ( sK4 = k1_xboole_0 ),
% 2.71/0.99      inference(superposition,[status(thm)],[c_1264,c_4029]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_3,plain,
% 2.71/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 2.71/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_4,plain,
% 2.71/0.99      ( ~ v1_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) ),
% 2.71/0.99      inference(cnf_transformation,[],[f94]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_309,plain,
% 2.71/0.99      ( k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) != k1_xboole_0 ),
% 2.71/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_4]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_1524,plain,
% 2.71/0.99      ( k1_relat_1(sK4) != k1_xboole_0 ),
% 2.71/0.99      inference(superposition,[status(thm)],[c_1429,c_309]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_4163,plain,
% 2.71/0.99      ( k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
% 2.71/0.99      inference(demodulation,[status(thm)],[c_4034,c_1524]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_9,plain,
% 2.71/0.99      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.71/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_4214,plain,
% 2.71/0.99      ( k1_xboole_0 != k1_xboole_0 ),
% 2.71/0.99      inference(light_normalisation,[status(thm)],[c_4163,c_9]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_4215,plain,
% 2.71/0.99      ( $false ),
% 2.71/0.99      inference(equality_resolution_simp,[status(thm)],[c_4214]) ).
% 2.71/0.99  
% 2.71/0.99  
% 2.71/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.71/0.99  
% 2.71/0.99  ------                               Statistics
% 2.71/0.99  
% 2.71/0.99  ------ General
% 2.71/0.99  
% 2.71/0.99  abstr_ref_over_cycles:                  0
% 2.71/0.99  abstr_ref_under_cycles:                 0
% 2.71/0.99  gc_basic_clause_elim:                   0
% 2.71/0.99  forced_gc_time:                         0
% 2.71/0.99  parsing_time:                           0.009
% 2.71/0.99  unif_index_cands_time:                  0.
% 2.71/0.99  unif_index_add_time:                    0.
% 2.71/0.99  orderings_time:                         0.
% 2.71/0.99  out_proof_time:                         0.009
% 2.71/0.99  total_time:                             0.155
% 2.71/0.99  num_of_symbols:                         58
% 2.71/0.99  num_of_terms:                           3546
% 2.71/0.99  
% 2.71/0.99  ------ Preprocessing
% 2.71/0.99  
% 2.71/0.99  num_of_splits:                          6
% 2.71/0.99  num_of_split_atoms:                     4
% 2.71/0.99  num_of_reused_defs:                     2
% 2.71/0.99  num_eq_ax_congr_red:                    23
% 2.71/0.99  num_of_sem_filtered_clauses:            1
% 2.71/0.99  num_of_subtypes:                        0
% 2.71/0.99  monotx_restored_types:                  0
% 2.71/0.99  sat_num_of_epr_types:                   0
% 2.71/0.99  sat_num_of_non_cyclic_types:            0
% 2.71/0.99  sat_guarded_non_collapsed_types:        0
% 2.71/0.99  num_pure_diseq_elim:                    0
% 2.71/0.99  simp_replaced_by:                       0
% 2.71/0.99  res_preprocessed:                       118
% 2.71/0.99  prep_upred:                             0
% 2.71/0.99  prep_unflattend:                        50
% 2.71/0.99  smt_new_axioms:                         0
% 2.71/0.99  pred_elim_cands:                        2
% 2.71/0.99  pred_elim:                              6
% 2.71/0.99  pred_elim_cl:                           11
% 2.71/0.99  pred_elim_cycles:                       11
% 2.71/0.99  merged_defs:                            0
% 2.71/0.99  merged_defs_ncl:                        0
% 2.71/0.99  bin_hyper_res:                          0
% 2.71/0.99  prep_cycles:                            4
% 2.71/0.99  pred_elim_time:                         0.011
% 2.71/0.99  splitting_time:                         0.
% 2.71/0.99  sem_filter_time:                        0.
% 2.71/0.99  monotx_time:                            0.
% 2.71/0.99  subtype_inf_time:                       0.
% 2.71/0.99  
% 2.71/0.99  ------ Problem properties
% 2.71/0.99  
% 2.71/0.99  clauses:                                25
% 2.71/0.99  conjectures:                            2
% 2.71/0.99  epr:                                    5
% 2.71/0.99  horn:                                   18
% 2.71/0.99  ground:                                 9
% 2.71/0.99  unary:                                  6
% 2.71/0.99  binary:                                 12
% 2.71/0.99  lits:                                   52
% 2.71/0.99  lits_eq:                                19
% 2.71/0.99  fd_pure:                                0
% 2.71/0.99  fd_pseudo:                              0
% 2.71/0.99  fd_cond:                                1
% 2.71/0.99  fd_pseudo_cond:                         1
% 2.71/0.99  ac_symbols:                             0
% 2.71/0.99  
% 2.71/0.99  ------ Propositional Solver
% 2.71/0.99  
% 2.71/0.99  prop_solver_calls:                      28
% 2.71/0.99  prop_fast_solver_calls:                 801
% 2.71/0.99  smt_solver_calls:                       0
% 2.71/0.99  smt_fast_solver_calls:                  0
% 2.71/0.99  prop_num_of_clauses:                    1473
% 2.71/0.99  prop_preprocess_simplified:             4805
% 2.71/0.99  prop_fo_subsumed:                       15
% 2.71/0.99  prop_solver_time:                       0.
% 2.71/0.99  smt_solver_time:                        0.
% 2.71/0.99  smt_fast_solver_time:                   0.
% 2.71/0.99  prop_fast_solver_time:                  0.
% 2.71/0.99  prop_unsat_core_time:                   0.
% 2.71/0.99  
% 2.71/0.99  ------ QBF
% 2.71/0.99  
% 2.71/0.99  qbf_q_res:                              0
% 2.71/0.99  qbf_num_tautologies:                    0
% 2.71/0.99  qbf_prep_cycles:                        0
% 2.71/0.99  
% 2.71/0.99  ------ BMC1
% 2.71/0.99  
% 2.71/0.99  bmc1_current_bound:                     -1
% 2.71/0.99  bmc1_last_solved_bound:                 -1
% 2.71/0.99  bmc1_unsat_core_size:                   -1
% 2.71/0.99  bmc1_unsat_core_parents_size:           -1
% 2.71/0.99  bmc1_merge_next_fun:                    0
% 2.71/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.71/0.99  
% 2.71/0.99  ------ Instantiation
% 2.71/0.99  
% 2.71/0.99  inst_num_of_clauses:                    427
% 2.71/0.99  inst_num_in_passive:                    68
% 2.71/0.99  inst_num_in_active:                     222
% 2.71/0.99  inst_num_in_unprocessed:                137
% 2.71/0.99  inst_num_of_loops:                      280
% 2.71/0.99  inst_num_of_learning_restarts:          0
% 2.71/0.99  inst_num_moves_active_passive:          55
% 2.71/0.99  inst_lit_activity:                      0
% 2.71/0.99  inst_lit_activity_moves:                0
% 2.71/0.99  inst_num_tautologies:                   0
% 2.71/0.99  inst_num_prop_implied:                  0
% 2.71/0.99  inst_num_existing_simplified:           0
% 2.71/0.99  inst_num_eq_res_simplified:             0
% 2.71/0.99  inst_num_child_elim:                    0
% 2.71/0.99  inst_num_of_dismatching_blockings:      199
% 2.71/0.99  inst_num_of_non_proper_insts:           414
% 2.71/0.99  inst_num_of_duplicates:                 0
% 2.71/0.99  inst_inst_num_from_inst_to_res:         0
% 2.71/0.99  inst_dismatching_checking_time:         0.
% 2.71/0.99  
% 2.71/0.99  ------ Resolution
% 2.71/0.99  
% 2.71/0.99  res_num_of_clauses:                     0
% 2.71/0.99  res_num_in_passive:                     0
% 2.71/0.99  res_num_in_active:                      0
% 2.71/0.99  res_num_of_loops:                       122
% 2.71/0.99  res_forward_subset_subsumed:            63
% 2.71/0.99  res_backward_subset_subsumed:           0
% 2.71/0.99  res_forward_subsumed:                   1
% 2.71/0.99  res_backward_subsumed:                  0
% 2.71/0.99  res_forward_subsumption_resolution:     0
% 2.71/0.99  res_backward_subsumption_resolution:    0
% 2.71/0.99  res_clause_to_clause_subsumption:       200
% 2.71/0.99  res_orphan_elimination:                 0
% 2.71/0.99  res_tautology_del:                      53
% 2.71/0.99  res_num_eq_res_simplified:              1
% 2.71/0.99  res_num_sel_changes:                    0
% 2.71/0.99  res_moves_from_active_to_pass:          0
% 2.71/0.99  
% 2.71/0.99  ------ Superposition
% 2.71/0.99  
% 2.71/0.99  sup_time_total:                         0.
% 2.71/0.99  sup_time_generating:                    0.
% 2.71/0.99  sup_time_sim_full:                      0.
% 2.71/0.99  sup_time_sim_immed:                     0.
% 2.71/0.99  
% 2.71/0.99  sup_num_of_clauses:                     49
% 2.71/0.99  sup_num_in_active:                      19
% 2.71/0.99  sup_num_in_passive:                     30
% 2.71/0.99  sup_num_of_loops:                       55
% 2.71/0.99  sup_fw_superposition:                   38
% 2.71/0.99  sup_bw_superposition:                   30
% 2.71/0.99  sup_immediate_simplified:               7
% 2.71/0.99  sup_given_eliminated:                   0
% 2.71/0.99  comparisons_done:                       0
% 2.71/0.99  comparisons_avoided:                    15
% 2.71/0.99  
% 2.71/0.99  ------ Simplifications
% 2.71/0.99  
% 2.71/0.99  
% 2.71/0.99  sim_fw_subset_subsumed:                 1
% 2.71/0.99  sim_bw_subset_subsumed:                 3
% 2.71/0.99  sim_fw_subsumed:                        2
% 2.71/0.99  sim_bw_subsumed:                        0
% 2.71/0.99  sim_fw_subsumption_res:                 0
% 2.71/0.99  sim_bw_subsumption_res:                 0
% 2.71/0.99  sim_tautology_del:                      0
% 2.71/0.99  sim_eq_tautology_del:                   0
% 2.71/0.99  sim_eq_res_simp:                        0
% 2.71/0.99  sim_fw_demodulated:                     0
% 2.71/0.99  sim_bw_demodulated:                     35
% 2.71/0.99  sim_light_normalised:                   15
% 2.71/0.99  sim_joinable_taut:                      0
% 2.71/0.99  sim_joinable_simp:                      0
% 2.71/0.99  sim_ac_normalised:                      0
% 2.71/0.99  sim_smt_subsumption:                    0
% 2.71/0.99  
%------------------------------------------------------------------------------
