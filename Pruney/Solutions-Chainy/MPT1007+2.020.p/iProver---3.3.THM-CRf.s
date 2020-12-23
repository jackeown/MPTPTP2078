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
% DateTime   : Thu Dec  3 12:04:46 EST 2020

% Result     : Theorem 6.88s
% Output     : CNFRefutation 6.88s
% Verified   : 
% Statistics : Number of formulae       :  204 (1927 expanded)
%              Number of clauses        :   90 ( 309 expanded)
%              Number of leaves         :   34 ( 514 expanded)
%              Depth                    :   29
%              Number of atoms          :  466 (4587 expanded)
%              Number of equality atoms :  204 (2058 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f56])).

fof(f58,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f57,f58])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f30,axiom,(
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

fof(f35,plain,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    inference(pure_predicate_removal,[],[f30])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f35])).

fof(f62,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f50,f62])).

fof(f102,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f33,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f33])).

fof(f54,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f55,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f54])).

fof(f65,plain,
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

fof(f66,plain,
    ( ~ r2_hidden(k1_funct_1(sK4,sK2),sK3)
    & k1_xboole_0 != sK3
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))
    & v1_funct_2(sK4,k1_tarski(sK2),sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f55,f65])).

fof(f113,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) ),
    inference(cnf_transformation,[],[f66])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f81,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f13])).

fof(f116,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f80,f81])).

fof(f117,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f79,f116])).

fof(f118,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f78,f117])).

fof(f119,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f77,f118])).

fof(f120,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f76,f119])).

fof(f123,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f75,f120])).

fof(f131,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) ),
    inference(definition_unfolding,[],[f113,f123])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f32,axiom,(
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

fof(f52,plain,(
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
    inference(ennf_transformation,[],[f32])).

fof(f53,plain,(
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
    inference(flattening,[],[f52])).

fof(f64,plain,(
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
    inference(nnf_transformation,[],[f53])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f112,plain,(
    v1_funct_2(sK4,k1_tarski(sK2),sK3) ),
    inference(cnf_transformation,[],[f66])).

fof(f132,plain,(
    v1_funct_2(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) ),
    inference(definition_unfolding,[],[f112,f123])).

fof(f114,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f66])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 )
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( k1_mcart_1(X0) = X1
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( k1_mcart_1(X0) = X1
      | ~ r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)) ) ),
    inference(definition_unfolding,[],[f100,f123])).

fof(f31,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r2_hidden(X1,X0)
         => ( r2_hidden(k2_mcart_1(X1),k2_relat_1(X0))
            & r2_hidden(k1_mcart_1(X1),k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(k2_mcart_1(X1),k2_relat_1(X0))
            & r2_hidden(k1_mcart_1(X1),k1_relat_1(X0)) )
          | ~ r2_hidden(X1,X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f103,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_mcart_1(X1),k1_relat_1(X0))
      | ~ r2_hidden(X1,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f115,plain,(
    ~ r2_hidden(k1_funct_1(sK4,sK2),sK3) ),
    inference(cnf_transformation,[],[f66])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f27])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f44])).

fof(f96,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f111,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f66])).

fof(f17,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f86,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f39])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f125,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f74,f120,f120])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
        | r2_hidden(X0,X1) )
      & ( ~ r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f20,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f89,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f121,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f89,f120])).

fof(f122,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f71,f121])).

fof(f127,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f82,f122,f123,f123])).

fof(f16,axiom,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f85,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f128,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f85,f123])).

fof(f15,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f84,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f24,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f94,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f124,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f72,f121])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1590,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1591,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2996,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1590,c_1591])).

cnf(c_26,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1579,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_1575,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1582,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3232,plain,
    ( k1_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1575,c_1582])).

cnf(c_34,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_38,negated_conjecture,
    ( v1_funct_2(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) ),
    inference(cnf_transformation,[],[f132])).

cnf(c_649,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != X1
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X2
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_38])).

cnf(c_650,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))
    | k1_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_649])).

cnf(c_36,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f114])).

cnf(c_652,plain,
    ( k1_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_650,c_37,c_36])).

cnf(c_3240,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_3232,c_652])).

cnf(c_3795,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3240,c_1575])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1586,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4816,plain,
    ( r2_hidden(X0,k2_zfmisc_1(k1_relat_1(sK4),sK3)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3795,c_1586])).

cnf(c_25,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2))
    | k1_mcart_1(X0) = X1 ),
    inference(cnf_transformation,[],[f130])).

cnf(c_1580,plain,
    ( k1_mcart_1(X0) = X1
    | r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4661,plain,
    ( k1_mcart_1(X0) = sK2
    | r2_hidden(X0,k2_zfmisc_1(k1_relat_1(sK4),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3240,c_1580])).

cnf(c_5665,plain,
    ( k1_mcart_1(X0) = sK2
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4816,c_4661])).

cnf(c_6437,plain,
    ( k1_mcart_1(sK1(sK4)) = sK2
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1579,c_5665])).

cnf(c_28,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k1_mcart_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1577,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(k1_mcart_1(X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_7685,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK1(sK4),X0) != iProver_top
    | r2_hidden(sK2,k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6437,c_1577])).

cnf(c_17777,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK2,k1_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1579,c_7685])).

cnf(c_42,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_35,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(sK4,sK2),sK3) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_43,plain,
    ( r2_hidden(k1_funct_1(sK4,sK2),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1774,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1775,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1774])).

cnf(c_22,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_17,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_479,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_22,c_17])).

cnf(c_483,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_479,c_21])).

cnf(c_484,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_483])).

cnf(c_1792,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))
    | r1_tarski(k2_relat_1(sK4),sK3) ),
    inference(instantiation,[status(thm)],[c_484])).

cnf(c_1793,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) != iProver_top
    | r1_tarski(k2_relat_1(sK4),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1792])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1780,plain,
    ( ~ r2_hidden(k1_funct_1(sK4,sK2),X0)
    | r2_hidden(k1_funct_1(sK4,sK2),sK3)
    | ~ r1_tarski(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1903,plain,
    ( ~ r2_hidden(k1_funct_1(sK4,sK2),k2_relat_1(sK4))
    | r2_hidden(k1_funct_1(sK4,sK2),sK3)
    | ~ r1_tarski(k2_relat_1(sK4),sK3) ),
    inference(instantiation,[status(thm)],[c_1780])).

cnf(c_1904,plain,
    ( r2_hidden(k1_funct_1(sK4,sK2),k2_relat_1(sK4)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,sK2),sK3) = iProver_top
    | r1_tarski(k2_relat_1(sK4),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1903])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_39,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_460,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_39])).

cnf(c_461,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_460])).

cnf(c_2272,plain,
    ( r2_hidden(k1_funct_1(sK4,sK2),k2_relat_1(sK4))
    | ~ r2_hidden(sK2,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_461])).

cnf(c_2275,plain,
    ( r2_hidden(k1_funct_1(sK4,sK2),k2_relat_1(sK4)) = iProver_top
    | r2_hidden(sK2,k1_relat_1(sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2272])).

cnf(c_17819,plain,
    ( sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_17777,c_42,c_43,c_1775,c_1793,c_1904,c_2275])).

cnf(c_11,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_445,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | k1_zfmisc_1(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_14])).

cnf(c_446,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(unflattening,[status(thm)],[c_445])).

cnf(c_1574,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_446])).

cnf(c_2316,plain,
    ( r2_hidden(sK4,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1575,c_1574])).

cnf(c_3793,plain,
    ( r2_hidden(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3240,c_2316])).

cnf(c_1589,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4326,plain,
    ( r2_hidden(sK4,X0) = iProver_top
    | r1_tarski(k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3793,c_1589])).

cnf(c_17882,plain,
    ( r2_hidden(k1_xboole_0,X0) = iProver_top
    | r1_tarski(k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),sK3)),X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_17819,c_4326])).

cnf(c_6,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_1587,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_6027,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
    | r2_hidden(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_1587])).

cnf(c_6144,plain,
    ( k5_xboole_0(k1_relat_1(sK4),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_relat_1(sK4)))) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | r2_hidden(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3240,c_6027])).

cnf(c_6147,plain,
    ( k5_xboole_0(k1_relat_1(sK4),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_relat_1(sK4)))) != k1_relat_1(sK4)
    | r2_hidden(sK2,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6144,c_3240])).

cnf(c_17887,plain,
    ( k5_xboole_0(k1_relat_1(k1_xboole_0),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_relat_1(k1_xboole_0)))) != k1_relat_1(k1_xboole_0)
    | r2_hidden(sK2,X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_17819,c_6147])).

cnf(c_10,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f128])).

cnf(c_3811,plain,
    ( k3_tarski(k1_relat_1(sK4)) = sK2 ),
    inference(superposition,[status(thm)],[c_3240,c_10])).

cnf(c_17900,plain,
    ( k3_tarski(k1_relat_1(k1_xboole_0)) = sK2 ),
    inference(demodulation,[status(thm)],[c_17819,c_3811])).

cnf(c_9,plain,
    ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_19,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_17920,plain,
    ( sK2 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_17900,c_9,c_19])).

cnf(c_17965,plain,
    ( k5_xboole_0(k1_relat_1(k1_xboole_0),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_relat_1(k1_xboole_0)))) != k1_relat_1(k1_xboole_0)
    | r2_hidden(k1_xboole_0,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17887,c_17920])).

cnf(c_4,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f124])).

cnf(c_17968,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | r2_hidden(k1_xboole_0,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17965,c_4,c_19])).

cnf(c_5,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1962,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_5,c_0])).

cnf(c_17969,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(k1_xboole_0,X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_17968,c_1962])).

cnf(c_17970,plain,
    ( r2_hidden(k1_xboole_0,X0) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_17969])).

cnf(c_17978,plain,
    ( r1_tarski(k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),sK3)),X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_17882,c_17970])).

cnf(c_17979,plain,
    ( r1_tarski(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)),X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17978,c_19])).

cnf(c_19763,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_2996,c_17979])).

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
% 0.13/0.34  % DateTime   : Tue Dec  1 10:14:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 6.88/1.54  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.88/1.54  
% 6.88/1.54  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.88/1.54  
% 6.88/1.54  ------  iProver source info
% 6.88/1.54  
% 6.88/1.54  git: date: 2020-06-30 10:37:57 +0100
% 6.88/1.54  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.88/1.54  git: non_committed_changes: false
% 6.88/1.54  git: last_make_outside_of_git: false
% 6.88/1.54  
% 6.88/1.54  ------ 
% 6.88/1.54  
% 6.88/1.54  ------ Input Options
% 6.88/1.54  
% 6.88/1.54  --out_options                           all
% 6.88/1.54  --tptp_safe_out                         true
% 6.88/1.54  --problem_path                          ""
% 6.88/1.54  --include_path                          ""
% 6.88/1.54  --clausifier                            res/vclausify_rel
% 6.88/1.54  --clausifier_options                    --mode clausify
% 6.88/1.54  --stdin                                 false
% 6.88/1.54  --stats_out                             all
% 6.88/1.54  
% 6.88/1.54  ------ General Options
% 6.88/1.54  
% 6.88/1.54  --fof                                   false
% 6.88/1.54  --time_out_real                         305.
% 6.88/1.54  --time_out_virtual                      -1.
% 6.88/1.54  --symbol_type_check                     false
% 6.88/1.54  --clausify_out                          false
% 6.88/1.54  --sig_cnt_out                           false
% 6.88/1.54  --trig_cnt_out                          false
% 6.88/1.54  --trig_cnt_out_tolerance                1.
% 6.88/1.54  --trig_cnt_out_sk_spl                   false
% 6.88/1.54  --abstr_cl_out                          false
% 6.88/1.54  
% 6.88/1.54  ------ Global Options
% 6.88/1.54  
% 6.88/1.54  --schedule                              default
% 6.88/1.54  --add_important_lit                     false
% 6.88/1.54  --prop_solver_per_cl                    1000
% 6.88/1.54  --min_unsat_core                        false
% 6.88/1.54  --soft_assumptions                      false
% 6.88/1.54  --soft_lemma_size                       3
% 6.88/1.54  --prop_impl_unit_size                   0
% 6.88/1.54  --prop_impl_unit                        []
% 6.88/1.54  --share_sel_clauses                     true
% 6.88/1.54  --reset_solvers                         false
% 6.88/1.54  --bc_imp_inh                            [conj_cone]
% 6.88/1.54  --conj_cone_tolerance                   3.
% 6.88/1.54  --extra_neg_conj                        none
% 6.88/1.54  --large_theory_mode                     true
% 6.88/1.54  --prolific_symb_bound                   200
% 6.88/1.54  --lt_threshold                          2000
% 6.88/1.54  --clause_weak_htbl                      true
% 6.88/1.54  --gc_record_bc_elim                     false
% 6.88/1.54  
% 6.88/1.54  ------ Preprocessing Options
% 6.88/1.54  
% 6.88/1.54  --preprocessing_flag                    true
% 6.88/1.54  --time_out_prep_mult                    0.1
% 6.88/1.54  --splitting_mode                        input
% 6.88/1.54  --splitting_grd                         true
% 6.88/1.54  --splitting_cvd                         false
% 6.88/1.54  --splitting_cvd_svl                     false
% 6.88/1.54  --splitting_nvd                         32
% 6.88/1.54  --sub_typing                            true
% 6.88/1.54  --prep_gs_sim                           true
% 6.88/1.54  --prep_unflatten                        true
% 6.88/1.54  --prep_res_sim                          true
% 6.88/1.54  --prep_upred                            true
% 6.88/1.54  --prep_sem_filter                       exhaustive
% 6.88/1.54  --prep_sem_filter_out                   false
% 6.88/1.54  --pred_elim                             true
% 6.88/1.54  --res_sim_input                         true
% 6.88/1.54  --eq_ax_congr_red                       true
% 6.88/1.54  --pure_diseq_elim                       true
% 6.88/1.54  --brand_transform                       false
% 6.88/1.54  --non_eq_to_eq                          false
% 6.88/1.54  --prep_def_merge                        true
% 6.88/1.54  --prep_def_merge_prop_impl              false
% 6.88/1.54  --prep_def_merge_mbd                    true
% 6.88/1.54  --prep_def_merge_tr_red                 false
% 6.88/1.54  --prep_def_merge_tr_cl                  false
% 6.88/1.54  --smt_preprocessing                     true
% 6.88/1.54  --smt_ac_axioms                         fast
% 6.88/1.54  --preprocessed_out                      false
% 6.88/1.54  --preprocessed_stats                    false
% 6.88/1.54  
% 6.88/1.54  ------ Abstraction refinement Options
% 6.88/1.54  
% 6.88/1.54  --abstr_ref                             []
% 6.88/1.54  --abstr_ref_prep                        false
% 6.88/1.54  --abstr_ref_until_sat                   false
% 6.88/1.54  --abstr_ref_sig_restrict                funpre
% 6.88/1.54  --abstr_ref_af_restrict_to_split_sk     false
% 6.88/1.54  --abstr_ref_under                       []
% 6.88/1.54  
% 6.88/1.54  ------ SAT Options
% 6.88/1.54  
% 6.88/1.54  --sat_mode                              false
% 6.88/1.54  --sat_fm_restart_options                ""
% 6.88/1.54  --sat_gr_def                            false
% 6.88/1.54  --sat_epr_types                         true
% 6.88/1.54  --sat_non_cyclic_types                  false
% 6.88/1.54  --sat_finite_models                     false
% 6.88/1.54  --sat_fm_lemmas                         false
% 6.88/1.54  --sat_fm_prep                           false
% 6.88/1.54  --sat_fm_uc_incr                        true
% 6.88/1.54  --sat_out_model                         small
% 6.88/1.54  --sat_out_clauses                       false
% 6.88/1.54  
% 6.88/1.54  ------ QBF Options
% 6.88/1.54  
% 6.88/1.54  --qbf_mode                              false
% 6.88/1.54  --qbf_elim_univ                         false
% 6.88/1.54  --qbf_dom_inst                          none
% 6.88/1.54  --qbf_dom_pre_inst                      false
% 6.88/1.54  --qbf_sk_in                             false
% 6.88/1.54  --qbf_pred_elim                         true
% 6.88/1.54  --qbf_split                             512
% 6.88/1.54  
% 6.88/1.54  ------ BMC1 Options
% 6.88/1.54  
% 6.88/1.54  --bmc1_incremental                      false
% 6.88/1.54  --bmc1_axioms                           reachable_all
% 6.88/1.54  --bmc1_min_bound                        0
% 6.88/1.54  --bmc1_max_bound                        -1
% 6.88/1.54  --bmc1_max_bound_default                -1
% 6.88/1.54  --bmc1_symbol_reachability              true
% 6.88/1.54  --bmc1_property_lemmas                  false
% 6.88/1.54  --bmc1_k_induction                      false
% 6.88/1.54  --bmc1_non_equiv_states                 false
% 6.88/1.54  --bmc1_deadlock                         false
% 6.88/1.54  --bmc1_ucm                              false
% 6.88/1.54  --bmc1_add_unsat_core                   none
% 6.88/1.54  --bmc1_unsat_core_children              false
% 6.88/1.54  --bmc1_unsat_core_extrapolate_axioms    false
% 6.88/1.54  --bmc1_out_stat                         full
% 6.88/1.54  --bmc1_ground_init                      false
% 6.88/1.54  --bmc1_pre_inst_next_state              false
% 6.88/1.54  --bmc1_pre_inst_state                   false
% 6.88/1.54  --bmc1_pre_inst_reach_state             false
% 6.88/1.54  --bmc1_out_unsat_core                   false
% 6.88/1.54  --bmc1_aig_witness_out                  false
% 6.88/1.54  --bmc1_verbose                          false
% 6.88/1.54  --bmc1_dump_clauses_tptp                false
% 6.88/1.54  --bmc1_dump_unsat_core_tptp             false
% 6.88/1.54  --bmc1_dump_file                        -
% 6.88/1.54  --bmc1_ucm_expand_uc_limit              128
% 6.88/1.54  --bmc1_ucm_n_expand_iterations          6
% 6.88/1.54  --bmc1_ucm_extend_mode                  1
% 6.88/1.54  --bmc1_ucm_init_mode                    2
% 6.88/1.54  --bmc1_ucm_cone_mode                    none
% 6.88/1.54  --bmc1_ucm_reduced_relation_type        0
% 6.88/1.54  --bmc1_ucm_relax_model                  4
% 6.88/1.54  --bmc1_ucm_full_tr_after_sat            true
% 6.88/1.54  --bmc1_ucm_expand_neg_assumptions       false
% 6.88/1.54  --bmc1_ucm_layered_model                none
% 6.88/1.54  --bmc1_ucm_max_lemma_size               10
% 6.88/1.54  
% 6.88/1.54  ------ AIG Options
% 6.88/1.54  
% 6.88/1.54  --aig_mode                              false
% 6.88/1.54  
% 6.88/1.54  ------ Instantiation Options
% 6.88/1.54  
% 6.88/1.54  --instantiation_flag                    true
% 6.88/1.54  --inst_sos_flag                         false
% 6.88/1.54  --inst_sos_phase                        true
% 6.88/1.54  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.88/1.54  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.88/1.54  --inst_lit_sel_side                     num_symb
% 6.88/1.54  --inst_solver_per_active                1400
% 6.88/1.54  --inst_solver_calls_frac                1.
% 6.88/1.54  --inst_passive_queue_type               priority_queues
% 6.88/1.54  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.88/1.54  --inst_passive_queues_freq              [25;2]
% 6.88/1.54  --inst_dismatching                      true
% 6.88/1.54  --inst_eager_unprocessed_to_passive     true
% 6.88/1.54  --inst_prop_sim_given                   true
% 6.88/1.54  --inst_prop_sim_new                     false
% 6.88/1.54  --inst_subs_new                         false
% 6.88/1.54  --inst_eq_res_simp                      false
% 6.88/1.54  --inst_subs_given                       false
% 6.88/1.54  --inst_orphan_elimination               true
% 6.88/1.54  --inst_learning_loop_flag               true
% 6.88/1.54  --inst_learning_start                   3000
% 6.88/1.54  --inst_learning_factor                  2
% 6.88/1.54  --inst_start_prop_sim_after_learn       3
% 6.88/1.54  --inst_sel_renew                        solver
% 6.88/1.54  --inst_lit_activity_flag                true
% 6.88/1.54  --inst_restr_to_given                   false
% 6.88/1.54  --inst_activity_threshold               500
% 6.88/1.54  --inst_out_proof                        true
% 6.88/1.54  
% 6.88/1.54  ------ Resolution Options
% 6.88/1.54  
% 6.88/1.54  --resolution_flag                       true
% 6.88/1.54  --res_lit_sel                           adaptive
% 6.88/1.54  --res_lit_sel_side                      none
% 6.88/1.54  --res_ordering                          kbo
% 6.88/1.54  --res_to_prop_solver                    active
% 6.88/1.54  --res_prop_simpl_new                    false
% 6.88/1.54  --res_prop_simpl_given                  true
% 6.88/1.54  --res_passive_queue_type                priority_queues
% 6.88/1.54  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.88/1.54  --res_passive_queues_freq               [15;5]
% 6.88/1.54  --res_forward_subs                      full
% 6.88/1.54  --res_backward_subs                     full
% 6.88/1.54  --res_forward_subs_resolution           true
% 6.88/1.54  --res_backward_subs_resolution          true
% 6.88/1.54  --res_orphan_elimination                true
% 6.88/1.54  --res_time_limit                        2.
% 6.88/1.54  --res_out_proof                         true
% 6.88/1.54  
% 6.88/1.54  ------ Superposition Options
% 6.88/1.54  
% 6.88/1.54  --superposition_flag                    true
% 6.88/1.54  --sup_passive_queue_type                priority_queues
% 6.88/1.54  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.88/1.54  --sup_passive_queues_freq               [8;1;4]
% 6.88/1.54  --demod_completeness_check              fast
% 6.88/1.54  --demod_use_ground                      true
% 6.88/1.54  --sup_to_prop_solver                    passive
% 6.88/1.54  --sup_prop_simpl_new                    true
% 6.88/1.54  --sup_prop_simpl_given                  true
% 6.88/1.54  --sup_fun_splitting                     false
% 6.88/1.54  --sup_smt_interval                      50000
% 6.88/1.54  
% 6.88/1.54  ------ Superposition Simplification Setup
% 6.88/1.54  
% 6.88/1.54  --sup_indices_passive                   []
% 6.88/1.54  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.88/1.54  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.88/1.54  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.88/1.54  --sup_full_triv                         [TrivRules;PropSubs]
% 6.88/1.54  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.88/1.54  --sup_full_bw                           [BwDemod]
% 6.88/1.54  --sup_immed_triv                        [TrivRules]
% 6.88/1.54  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.88/1.54  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.88/1.54  --sup_immed_bw_main                     []
% 6.88/1.54  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.88/1.54  --sup_input_triv                        [Unflattening;TrivRules]
% 6.88/1.54  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.88/1.54  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.88/1.54  
% 6.88/1.54  ------ Combination Options
% 6.88/1.54  
% 6.88/1.54  --comb_res_mult                         3
% 6.88/1.54  --comb_sup_mult                         2
% 6.88/1.54  --comb_inst_mult                        10
% 6.88/1.54  
% 6.88/1.54  ------ Debug Options
% 6.88/1.54  
% 6.88/1.54  --dbg_backtrace                         false
% 6.88/1.54  --dbg_dump_prop_clauses                 false
% 6.88/1.54  --dbg_dump_prop_clauses_file            -
% 6.88/1.54  --dbg_out_stat                          false
% 6.88/1.54  ------ Parsing...
% 6.88/1.54  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.88/1.54  
% 6.88/1.54  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 6.88/1.54  
% 6.88/1.54  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.88/1.54  
% 6.88/1.54  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.88/1.54  ------ Proving...
% 6.88/1.54  ------ Problem Properties 
% 6.88/1.54  
% 6.88/1.54  
% 6.88/1.54  clauses                                 32
% 6.88/1.54  conjectures                             3
% 6.88/1.54  EPR                                     2
% 6.88/1.54  Horn                                    28
% 6.88/1.54  unary                                   13
% 6.88/1.54  binary                                  11
% 6.88/1.54  lits                                    60
% 6.88/1.54  lits eq                                 20
% 6.88/1.54  fd_pure                                 0
% 6.88/1.54  fd_pseudo                               0
% 6.88/1.54  fd_cond                                 1
% 6.88/1.54  fd_pseudo_cond                          1
% 6.88/1.54  AC symbols                              0
% 6.88/1.54  
% 6.88/1.54  ------ Schedule dynamic 5 is on 
% 6.88/1.54  
% 6.88/1.54  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.88/1.54  
% 6.88/1.54  
% 6.88/1.54  ------ 
% 6.88/1.54  Current options:
% 6.88/1.54  ------ 
% 6.88/1.54  
% 6.88/1.54  ------ Input Options
% 6.88/1.54  
% 6.88/1.54  --out_options                           all
% 6.88/1.54  --tptp_safe_out                         true
% 6.88/1.54  --problem_path                          ""
% 6.88/1.54  --include_path                          ""
% 6.88/1.54  --clausifier                            res/vclausify_rel
% 6.88/1.54  --clausifier_options                    --mode clausify
% 6.88/1.54  --stdin                                 false
% 6.88/1.54  --stats_out                             all
% 6.88/1.55  
% 6.88/1.55  ------ General Options
% 6.88/1.55  
% 6.88/1.55  --fof                                   false
% 6.88/1.55  --time_out_real                         305.
% 6.88/1.55  --time_out_virtual                      -1.
% 6.88/1.55  --symbol_type_check                     false
% 6.88/1.55  --clausify_out                          false
% 6.88/1.55  --sig_cnt_out                           false
% 6.88/1.55  --trig_cnt_out                          false
% 6.88/1.55  --trig_cnt_out_tolerance                1.
% 6.88/1.55  --trig_cnt_out_sk_spl                   false
% 6.88/1.55  --abstr_cl_out                          false
% 6.88/1.55  
% 6.88/1.55  ------ Global Options
% 6.88/1.55  
% 6.88/1.55  --schedule                              default
% 6.88/1.55  --add_important_lit                     false
% 6.88/1.55  --prop_solver_per_cl                    1000
% 6.88/1.55  --min_unsat_core                        false
% 6.88/1.55  --soft_assumptions                      false
% 6.88/1.55  --soft_lemma_size                       3
% 6.88/1.55  --prop_impl_unit_size                   0
% 6.88/1.55  --prop_impl_unit                        []
% 6.88/1.55  --share_sel_clauses                     true
% 6.88/1.55  --reset_solvers                         false
% 6.88/1.55  --bc_imp_inh                            [conj_cone]
% 6.88/1.55  --conj_cone_tolerance                   3.
% 6.88/1.55  --extra_neg_conj                        none
% 6.88/1.55  --large_theory_mode                     true
% 6.88/1.55  --prolific_symb_bound                   200
% 6.88/1.55  --lt_threshold                          2000
% 6.88/1.55  --clause_weak_htbl                      true
% 6.88/1.55  --gc_record_bc_elim                     false
% 6.88/1.55  
% 6.88/1.55  ------ Preprocessing Options
% 6.88/1.55  
% 6.88/1.55  --preprocessing_flag                    true
% 6.88/1.55  --time_out_prep_mult                    0.1
% 6.88/1.55  --splitting_mode                        input
% 6.88/1.55  --splitting_grd                         true
% 6.88/1.55  --splitting_cvd                         false
% 6.88/1.55  --splitting_cvd_svl                     false
% 6.88/1.55  --splitting_nvd                         32
% 6.88/1.55  --sub_typing                            true
% 6.88/1.55  --prep_gs_sim                           true
% 6.88/1.55  --prep_unflatten                        true
% 6.88/1.55  --prep_res_sim                          true
% 6.88/1.55  --prep_upred                            true
% 6.88/1.55  --prep_sem_filter                       exhaustive
% 6.88/1.55  --prep_sem_filter_out                   false
% 6.88/1.55  --pred_elim                             true
% 6.88/1.55  --res_sim_input                         true
% 6.88/1.55  --eq_ax_congr_red                       true
% 6.88/1.55  --pure_diseq_elim                       true
% 6.88/1.55  --brand_transform                       false
% 6.88/1.55  --non_eq_to_eq                          false
% 6.88/1.55  --prep_def_merge                        true
% 6.88/1.55  --prep_def_merge_prop_impl              false
% 6.88/1.55  --prep_def_merge_mbd                    true
% 6.88/1.55  --prep_def_merge_tr_red                 false
% 6.88/1.55  --prep_def_merge_tr_cl                  false
% 6.88/1.55  --smt_preprocessing                     true
% 6.88/1.55  --smt_ac_axioms                         fast
% 6.88/1.55  --preprocessed_out                      false
% 6.88/1.55  --preprocessed_stats                    false
% 6.88/1.55  
% 6.88/1.55  ------ Abstraction refinement Options
% 6.88/1.55  
% 6.88/1.55  --abstr_ref                             []
% 6.88/1.55  --abstr_ref_prep                        false
% 6.88/1.55  --abstr_ref_until_sat                   false
% 6.88/1.55  --abstr_ref_sig_restrict                funpre
% 6.88/1.55  --abstr_ref_af_restrict_to_split_sk     false
% 6.88/1.55  --abstr_ref_under                       []
% 6.88/1.55  
% 6.88/1.55  ------ SAT Options
% 6.88/1.55  
% 6.88/1.55  --sat_mode                              false
% 6.88/1.55  --sat_fm_restart_options                ""
% 6.88/1.55  --sat_gr_def                            false
% 6.88/1.55  --sat_epr_types                         true
% 6.88/1.55  --sat_non_cyclic_types                  false
% 6.88/1.55  --sat_finite_models                     false
% 6.88/1.55  --sat_fm_lemmas                         false
% 6.88/1.55  --sat_fm_prep                           false
% 6.88/1.55  --sat_fm_uc_incr                        true
% 6.88/1.55  --sat_out_model                         small
% 6.88/1.55  --sat_out_clauses                       false
% 6.88/1.55  
% 6.88/1.55  ------ QBF Options
% 6.88/1.55  
% 6.88/1.55  --qbf_mode                              false
% 6.88/1.55  --qbf_elim_univ                         false
% 6.88/1.55  --qbf_dom_inst                          none
% 6.88/1.55  --qbf_dom_pre_inst                      false
% 6.88/1.55  --qbf_sk_in                             false
% 6.88/1.55  --qbf_pred_elim                         true
% 6.88/1.55  --qbf_split                             512
% 6.88/1.55  
% 6.88/1.55  ------ BMC1 Options
% 6.88/1.55  
% 6.88/1.55  --bmc1_incremental                      false
% 6.88/1.55  --bmc1_axioms                           reachable_all
% 6.88/1.55  --bmc1_min_bound                        0
% 6.88/1.55  --bmc1_max_bound                        -1
% 6.88/1.55  --bmc1_max_bound_default                -1
% 6.88/1.55  --bmc1_symbol_reachability              true
% 6.88/1.55  --bmc1_property_lemmas                  false
% 6.88/1.55  --bmc1_k_induction                      false
% 6.88/1.55  --bmc1_non_equiv_states                 false
% 6.88/1.55  --bmc1_deadlock                         false
% 6.88/1.55  --bmc1_ucm                              false
% 6.88/1.55  --bmc1_add_unsat_core                   none
% 6.88/1.55  --bmc1_unsat_core_children              false
% 6.88/1.55  --bmc1_unsat_core_extrapolate_axioms    false
% 6.88/1.55  --bmc1_out_stat                         full
% 6.88/1.55  --bmc1_ground_init                      false
% 6.88/1.55  --bmc1_pre_inst_next_state              false
% 6.88/1.55  --bmc1_pre_inst_state                   false
% 6.88/1.55  --bmc1_pre_inst_reach_state             false
% 6.88/1.55  --bmc1_out_unsat_core                   false
% 6.88/1.55  --bmc1_aig_witness_out                  false
% 6.88/1.55  --bmc1_verbose                          false
% 6.88/1.55  --bmc1_dump_clauses_tptp                false
% 6.88/1.55  --bmc1_dump_unsat_core_tptp             false
% 6.88/1.55  --bmc1_dump_file                        -
% 6.88/1.55  --bmc1_ucm_expand_uc_limit              128
% 6.88/1.55  --bmc1_ucm_n_expand_iterations          6
% 6.88/1.55  --bmc1_ucm_extend_mode                  1
% 6.88/1.55  --bmc1_ucm_init_mode                    2
% 6.88/1.55  --bmc1_ucm_cone_mode                    none
% 6.88/1.55  --bmc1_ucm_reduced_relation_type        0
% 6.88/1.55  --bmc1_ucm_relax_model                  4
% 6.88/1.55  --bmc1_ucm_full_tr_after_sat            true
% 6.88/1.55  --bmc1_ucm_expand_neg_assumptions       false
% 6.88/1.55  --bmc1_ucm_layered_model                none
% 6.88/1.55  --bmc1_ucm_max_lemma_size               10
% 6.88/1.55  
% 6.88/1.55  ------ AIG Options
% 6.88/1.55  
% 6.88/1.55  --aig_mode                              false
% 6.88/1.55  
% 6.88/1.55  ------ Instantiation Options
% 6.88/1.55  
% 6.88/1.55  --instantiation_flag                    true
% 6.88/1.55  --inst_sos_flag                         false
% 6.88/1.55  --inst_sos_phase                        true
% 6.88/1.55  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.88/1.55  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.88/1.55  --inst_lit_sel_side                     none
% 6.88/1.55  --inst_solver_per_active                1400
% 6.88/1.55  --inst_solver_calls_frac                1.
% 6.88/1.55  --inst_passive_queue_type               priority_queues
% 6.88/1.55  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.88/1.55  --inst_passive_queues_freq              [25;2]
% 6.88/1.55  --inst_dismatching                      true
% 6.88/1.55  --inst_eager_unprocessed_to_passive     true
% 6.88/1.55  --inst_prop_sim_given                   true
% 6.88/1.55  --inst_prop_sim_new                     false
% 6.88/1.55  --inst_subs_new                         false
% 6.88/1.55  --inst_eq_res_simp                      false
% 6.88/1.55  --inst_subs_given                       false
% 6.88/1.55  --inst_orphan_elimination               true
% 6.88/1.55  --inst_learning_loop_flag               true
% 6.88/1.55  --inst_learning_start                   3000
% 6.88/1.55  --inst_learning_factor                  2
% 6.88/1.55  --inst_start_prop_sim_after_learn       3
% 6.88/1.55  --inst_sel_renew                        solver
% 6.88/1.55  --inst_lit_activity_flag                true
% 6.88/1.55  --inst_restr_to_given                   false
% 6.88/1.55  --inst_activity_threshold               500
% 6.88/1.55  --inst_out_proof                        true
% 6.88/1.55  
% 6.88/1.55  ------ Resolution Options
% 6.88/1.55  
% 6.88/1.55  --resolution_flag                       false
% 6.88/1.55  --res_lit_sel                           adaptive
% 6.88/1.55  --res_lit_sel_side                      none
% 6.88/1.55  --res_ordering                          kbo
% 6.88/1.55  --res_to_prop_solver                    active
% 6.88/1.55  --res_prop_simpl_new                    false
% 6.88/1.55  --res_prop_simpl_given                  true
% 6.88/1.55  --res_passive_queue_type                priority_queues
% 6.88/1.55  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.88/1.55  --res_passive_queues_freq               [15;5]
% 6.88/1.55  --res_forward_subs                      full
% 6.88/1.55  --res_backward_subs                     full
% 6.88/1.55  --res_forward_subs_resolution           true
% 6.88/1.55  --res_backward_subs_resolution          true
% 6.88/1.55  --res_orphan_elimination                true
% 6.88/1.55  --res_time_limit                        2.
% 6.88/1.55  --res_out_proof                         true
% 6.88/1.55  
% 6.88/1.55  ------ Superposition Options
% 6.88/1.55  
% 6.88/1.55  --superposition_flag                    true
% 6.88/1.55  --sup_passive_queue_type                priority_queues
% 6.88/1.55  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.88/1.55  --sup_passive_queues_freq               [8;1;4]
% 6.88/1.55  --demod_completeness_check              fast
% 6.88/1.55  --demod_use_ground                      true
% 6.88/1.55  --sup_to_prop_solver                    passive
% 6.88/1.55  --sup_prop_simpl_new                    true
% 6.88/1.55  --sup_prop_simpl_given                  true
% 6.88/1.55  --sup_fun_splitting                     false
% 6.88/1.55  --sup_smt_interval                      50000
% 6.88/1.55  
% 6.88/1.55  ------ Superposition Simplification Setup
% 6.88/1.55  
% 6.88/1.55  --sup_indices_passive                   []
% 6.88/1.55  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.88/1.55  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.88/1.55  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.88/1.55  --sup_full_triv                         [TrivRules;PropSubs]
% 6.88/1.55  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.88/1.55  --sup_full_bw                           [BwDemod]
% 6.88/1.55  --sup_immed_triv                        [TrivRules]
% 6.88/1.55  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.88/1.55  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.88/1.55  --sup_immed_bw_main                     []
% 6.88/1.55  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.88/1.55  --sup_input_triv                        [Unflattening;TrivRules]
% 6.88/1.55  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.88/1.55  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.88/1.55  
% 6.88/1.55  ------ Combination Options
% 6.88/1.55  
% 6.88/1.55  --comb_res_mult                         3
% 6.88/1.55  --comb_sup_mult                         2
% 6.88/1.55  --comb_inst_mult                        10
% 6.88/1.55  
% 6.88/1.55  ------ Debug Options
% 6.88/1.55  
% 6.88/1.55  --dbg_backtrace                         false
% 6.88/1.55  --dbg_dump_prop_clauses                 false
% 6.88/1.55  --dbg_dump_prop_clauses_file            -
% 6.88/1.55  --dbg_out_stat                          false
% 6.88/1.55  
% 6.88/1.55  
% 6.88/1.55  
% 6.88/1.55  
% 6.88/1.55  ------ Proving...
% 6.88/1.55  
% 6.88/1.55  
% 6.88/1.55  % SZS status Theorem for theBenchmark.p
% 6.88/1.55  
% 6.88/1.55   Resolution empty clause
% 6.88/1.55  
% 6.88/1.55  % SZS output start CNFRefutation for theBenchmark.p
% 6.88/1.55  
% 6.88/1.55  fof(f2,axiom,(
% 6.88/1.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 6.88/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.88/1.55  
% 6.88/1.55  fof(f37,plain,(
% 6.88/1.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 6.88/1.55    inference(ennf_transformation,[],[f2])).
% 6.88/1.55  
% 6.88/1.55  fof(f56,plain,(
% 6.88/1.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 6.88/1.55    inference(nnf_transformation,[],[f37])).
% 6.88/1.55  
% 6.88/1.55  fof(f57,plain,(
% 6.88/1.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 6.88/1.55    inference(rectify,[],[f56])).
% 6.88/1.55  
% 6.88/1.55  fof(f58,plain,(
% 6.88/1.55    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 6.88/1.55    introduced(choice_axiom,[])).
% 6.88/1.55  
% 6.88/1.55  fof(f59,plain,(
% 6.88/1.55    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 6.88/1.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f57,f58])).
% 6.88/1.55  
% 6.88/1.55  fof(f69,plain,(
% 6.88/1.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 6.88/1.55    inference(cnf_transformation,[],[f59])).
% 6.88/1.55  
% 6.88/1.55  fof(f70,plain,(
% 6.88/1.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 6.88/1.55    inference(cnf_transformation,[],[f59])).
% 6.88/1.55  
% 6.88/1.55  fof(f30,axiom,(
% 6.88/1.55    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5,X6] : ((r2_hidden(X6,X1) & r2_hidden(X5,X6) & r2_hidden(X4,X5) & r2_hidden(X3,X4) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 6.88/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.88/1.55  
% 6.88/1.55  fof(f35,plain,(
% 6.88/1.55    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 6.88/1.55    inference(pure_predicate_removal,[],[f30])).
% 6.88/1.55  
% 6.88/1.55  fof(f50,plain,(
% 6.88/1.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 6.88/1.55    inference(ennf_transformation,[],[f35])).
% 6.88/1.55  
% 6.88/1.55  fof(f62,plain,(
% 6.88/1.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 6.88/1.55    introduced(choice_axiom,[])).
% 6.88/1.55  
% 6.88/1.55  fof(f63,plain,(
% 6.88/1.55    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 6.88/1.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f50,f62])).
% 6.88/1.55  
% 6.88/1.55  fof(f102,plain,(
% 6.88/1.55    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 6.88/1.55    inference(cnf_transformation,[],[f63])).
% 6.88/1.55  
% 6.88/1.55  fof(f33,conjecture,(
% 6.88/1.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 6.88/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.88/1.55  
% 6.88/1.55  fof(f34,negated_conjecture,(
% 6.88/1.55    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 6.88/1.55    inference(negated_conjecture,[],[f33])).
% 6.88/1.55  
% 6.88/1.55  fof(f54,plain,(
% 6.88/1.55    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 6.88/1.55    inference(ennf_transformation,[],[f34])).
% 6.88/1.55  
% 6.88/1.55  fof(f55,plain,(
% 6.88/1.55    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 6.88/1.55    inference(flattening,[],[f54])).
% 6.88/1.55  
% 6.88/1.55  fof(f65,plain,(
% 6.88/1.55    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (~r2_hidden(k1_funct_1(sK4,sK2),sK3) & k1_xboole_0 != sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) & v1_funct_2(sK4,k1_tarski(sK2),sK3) & v1_funct_1(sK4))),
% 6.88/1.55    introduced(choice_axiom,[])).
% 6.88/1.55  
% 6.88/1.55  fof(f66,plain,(
% 6.88/1.55    ~r2_hidden(k1_funct_1(sK4,sK2),sK3) & k1_xboole_0 != sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) & v1_funct_2(sK4,k1_tarski(sK2),sK3) & v1_funct_1(sK4)),
% 6.88/1.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f55,f65])).
% 6.88/1.55  
% 6.88/1.55  fof(f113,plain,(
% 6.88/1.55    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))),
% 6.88/1.55    inference(cnf_transformation,[],[f66])).
% 6.88/1.55  
% 6.88/1.55  fof(f7,axiom,(
% 6.88/1.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 6.88/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.88/1.55  
% 6.88/1.55  fof(f75,plain,(
% 6.88/1.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 6.88/1.55    inference(cnf_transformation,[],[f7])).
% 6.88/1.55  
% 6.88/1.55  fof(f8,axiom,(
% 6.88/1.55    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 6.88/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.88/1.55  
% 6.88/1.55  fof(f76,plain,(
% 6.88/1.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 6.88/1.55    inference(cnf_transformation,[],[f8])).
% 6.88/1.55  
% 6.88/1.55  fof(f9,axiom,(
% 6.88/1.55    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 6.88/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.88/1.55  
% 6.88/1.55  fof(f77,plain,(
% 6.88/1.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 6.88/1.55    inference(cnf_transformation,[],[f9])).
% 6.88/1.55  
% 6.88/1.55  fof(f10,axiom,(
% 6.88/1.55    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 6.88/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.88/1.55  
% 6.88/1.55  fof(f78,plain,(
% 6.88/1.55    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 6.88/1.55    inference(cnf_transformation,[],[f10])).
% 6.88/1.55  
% 6.88/1.55  fof(f11,axiom,(
% 6.88/1.55    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 6.88/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.88/1.55  
% 6.88/1.55  fof(f79,plain,(
% 6.88/1.55    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 6.88/1.55    inference(cnf_transformation,[],[f11])).
% 6.88/1.55  
% 6.88/1.55  fof(f12,axiom,(
% 6.88/1.55    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 6.88/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.88/1.55  
% 6.88/1.55  fof(f80,plain,(
% 6.88/1.55    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 6.88/1.55    inference(cnf_transformation,[],[f12])).
% 6.88/1.55  
% 6.88/1.55  fof(f13,axiom,(
% 6.88/1.55    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 6.88/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.88/1.55  
% 6.88/1.55  fof(f81,plain,(
% 6.88/1.55    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 6.88/1.55    inference(cnf_transformation,[],[f13])).
% 6.88/1.55  
% 6.88/1.55  fof(f116,plain,(
% 6.88/1.55    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 6.88/1.55    inference(definition_unfolding,[],[f80,f81])).
% 6.88/1.55  
% 6.88/1.55  fof(f117,plain,(
% 6.88/1.55    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 6.88/1.55    inference(definition_unfolding,[],[f79,f116])).
% 6.88/1.55  
% 6.88/1.55  fof(f118,plain,(
% 6.88/1.55    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 6.88/1.55    inference(definition_unfolding,[],[f78,f117])).
% 6.88/1.55  
% 6.88/1.55  fof(f119,plain,(
% 6.88/1.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 6.88/1.55    inference(definition_unfolding,[],[f77,f118])).
% 6.88/1.55  
% 6.88/1.55  fof(f120,plain,(
% 6.88/1.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 6.88/1.55    inference(definition_unfolding,[],[f76,f119])).
% 6.88/1.55  
% 6.88/1.55  fof(f123,plain,(
% 6.88/1.55    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 6.88/1.55    inference(definition_unfolding,[],[f75,f120])).
% 6.88/1.55  
% 6.88/1.55  fof(f131,plain,(
% 6.88/1.55    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))),
% 6.88/1.55    inference(definition_unfolding,[],[f113,f123])).
% 6.88/1.55  
% 6.88/1.55  fof(f28,axiom,(
% 6.88/1.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 6.88/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.88/1.55  
% 6.88/1.55  fof(f48,plain,(
% 6.88/1.55    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.88/1.55    inference(ennf_transformation,[],[f28])).
% 6.88/1.55  
% 6.88/1.55  fof(f99,plain,(
% 6.88/1.55    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.88/1.55    inference(cnf_transformation,[],[f48])).
% 6.88/1.55  
% 6.88/1.55  fof(f32,axiom,(
% 6.88/1.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 6.88/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.88/1.55  
% 6.88/1.55  fof(f52,plain,(
% 6.88/1.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.88/1.55    inference(ennf_transformation,[],[f32])).
% 6.88/1.55  
% 6.88/1.55  fof(f53,plain,(
% 6.88/1.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.88/1.55    inference(flattening,[],[f52])).
% 6.88/1.55  
% 6.88/1.55  fof(f64,plain,(
% 6.88/1.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.88/1.55    inference(nnf_transformation,[],[f53])).
% 6.88/1.55  
% 6.88/1.55  fof(f105,plain,(
% 6.88/1.55    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.88/1.55    inference(cnf_transformation,[],[f64])).
% 6.88/1.55  
% 6.88/1.55  fof(f112,plain,(
% 6.88/1.55    v1_funct_2(sK4,k1_tarski(sK2),sK3)),
% 6.88/1.55    inference(cnf_transformation,[],[f66])).
% 6.88/1.55  
% 6.88/1.55  fof(f132,plain,(
% 6.88/1.55    v1_funct_2(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)),
% 6.88/1.55    inference(definition_unfolding,[],[f112,f123])).
% 6.88/1.55  
% 6.88/1.55  fof(f114,plain,(
% 6.88/1.55    k1_xboole_0 != sK3),
% 6.88/1.55    inference(cnf_transformation,[],[f66])).
% 6.88/1.55  
% 6.88/1.55  fof(f18,axiom,(
% 6.88/1.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 6.88/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.88/1.55  
% 6.88/1.55  fof(f38,plain,(
% 6.88/1.55    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.88/1.55    inference(ennf_transformation,[],[f18])).
% 6.88/1.55  
% 6.88/1.55  fof(f87,plain,(
% 6.88/1.55    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.88/1.55    inference(cnf_transformation,[],[f38])).
% 6.88/1.55  
% 6.88/1.55  fof(f29,axiom,(
% 6.88/1.55    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) => (r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1))),
% 6.88/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.88/1.55  
% 6.88/1.55  fof(f49,plain,(
% 6.88/1.55    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1) | ~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)))),
% 6.88/1.55    inference(ennf_transformation,[],[f29])).
% 6.88/1.55  
% 6.88/1.55  fof(f100,plain,(
% 6.88/1.55    ( ! [X2,X0,X1] : (k1_mcart_1(X0) = X1 | ~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))) )),
% 6.88/1.55    inference(cnf_transformation,[],[f49])).
% 6.88/1.55  
% 6.88/1.55  fof(f130,plain,(
% 6.88/1.55    ( ! [X2,X0,X1] : (k1_mcart_1(X0) = X1 | ~r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2))) )),
% 6.88/1.55    inference(definition_unfolding,[],[f100,f123])).
% 6.88/1.55  
% 6.88/1.55  fof(f31,axiom,(
% 6.88/1.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r2_hidden(X1,X0) => (r2_hidden(k2_mcart_1(X1),k2_relat_1(X0)) & r2_hidden(k1_mcart_1(X1),k1_relat_1(X0)))))),
% 6.88/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.88/1.55  
% 6.88/1.55  fof(f51,plain,(
% 6.88/1.55    ! [X0] : (! [X1] : ((r2_hidden(k2_mcart_1(X1),k2_relat_1(X0)) & r2_hidden(k1_mcart_1(X1),k1_relat_1(X0))) | ~r2_hidden(X1,X0)) | ~v1_relat_1(X0))),
% 6.88/1.55    inference(ennf_transformation,[],[f31])).
% 6.88/1.55  
% 6.88/1.55  fof(f103,plain,(
% 6.88/1.55    ( ! [X0,X1] : (r2_hidden(k1_mcart_1(X1),k1_relat_1(X0)) | ~r2_hidden(X1,X0) | ~v1_relat_1(X0)) )),
% 6.88/1.55    inference(cnf_transformation,[],[f51])).
% 6.88/1.55  
% 6.88/1.55  fof(f115,plain,(
% 6.88/1.55    ~r2_hidden(k1_funct_1(sK4,sK2),sK3)),
% 6.88/1.55    inference(cnf_transformation,[],[f66])).
% 6.88/1.55  
% 6.88/1.55  fof(f26,axiom,(
% 6.88/1.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 6.88/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.88/1.55  
% 6.88/1.55  fof(f46,plain,(
% 6.88/1.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.88/1.55    inference(ennf_transformation,[],[f26])).
% 6.88/1.55  
% 6.88/1.55  fof(f97,plain,(
% 6.88/1.55    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.88/1.55    inference(cnf_transformation,[],[f46])).
% 6.88/1.55  
% 6.88/1.55  fof(f27,axiom,(
% 6.88/1.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 6.88/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.88/1.55  
% 6.88/1.55  fof(f36,plain,(
% 6.88/1.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 6.88/1.55    inference(pure_predicate_removal,[],[f27])).
% 6.88/1.55  
% 6.88/1.55  fof(f47,plain,(
% 6.88/1.55    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.88/1.55    inference(ennf_transformation,[],[f36])).
% 6.88/1.55  
% 6.88/1.55  fof(f98,plain,(
% 6.88/1.55    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.88/1.55    inference(cnf_transformation,[],[f47])).
% 6.88/1.55  
% 6.88/1.55  fof(f23,axiom,(
% 6.88/1.55    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 6.88/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.88/1.55  
% 6.88/1.55  fof(f43,plain,(
% 6.88/1.55    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 6.88/1.55    inference(ennf_transformation,[],[f23])).
% 6.88/1.55  
% 6.88/1.55  fof(f61,plain,(
% 6.88/1.55    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 6.88/1.55    inference(nnf_transformation,[],[f43])).
% 6.88/1.55  
% 6.88/1.55  fof(f92,plain,(
% 6.88/1.55    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 6.88/1.55    inference(cnf_transformation,[],[f61])).
% 6.88/1.55  
% 6.88/1.55  fof(f68,plain,(
% 6.88/1.55    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 6.88/1.55    inference(cnf_transformation,[],[f59])).
% 6.88/1.55  
% 6.88/1.55  fof(f25,axiom,(
% 6.88/1.55    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 6.88/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.88/1.55  
% 6.88/1.55  fof(f44,plain,(
% 6.88/1.55    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 6.88/1.55    inference(ennf_transformation,[],[f25])).
% 6.88/1.55  
% 6.88/1.55  fof(f45,plain,(
% 6.88/1.55    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 6.88/1.55    inference(flattening,[],[f44])).
% 6.88/1.55  
% 6.88/1.55  fof(f96,plain,(
% 6.88/1.55    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 6.88/1.55    inference(cnf_transformation,[],[f45])).
% 6.88/1.55  
% 6.88/1.55  fof(f111,plain,(
% 6.88/1.55    v1_funct_1(sK4)),
% 6.88/1.55    inference(cnf_transformation,[],[f66])).
% 6.88/1.55  
% 6.88/1.55  fof(f17,axiom,(
% 6.88/1.55    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 6.88/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.88/1.55  
% 6.88/1.55  fof(f86,plain,(
% 6.88/1.55    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 6.88/1.55    inference(cnf_transformation,[],[f17])).
% 6.88/1.55  
% 6.88/1.55  fof(f21,axiom,(
% 6.88/1.55    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 6.88/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.88/1.55  
% 6.88/1.55  fof(f39,plain,(
% 6.88/1.55    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 6.88/1.55    inference(ennf_transformation,[],[f21])).
% 6.88/1.55  
% 6.88/1.55  fof(f40,plain,(
% 6.88/1.55    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 6.88/1.55    inference(flattening,[],[f39])).
% 6.88/1.55  
% 6.88/1.55  fof(f90,plain,(
% 6.88/1.55    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 6.88/1.55    inference(cnf_transformation,[],[f40])).
% 6.88/1.55  
% 6.88/1.55  fof(f6,axiom,(
% 6.88/1.55    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 6.88/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.88/1.55  
% 6.88/1.55  fof(f74,plain,(
% 6.88/1.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 6.88/1.55    inference(cnf_transformation,[],[f6])).
% 6.88/1.55  
% 6.88/1.55  fof(f125,plain,(
% 6.88/1.55    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) )),
% 6.88/1.55    inference(definition_unfolding,[],[f74,f120,f120])).
% 6.88/1.55  
% 6.88/1.55  fof(f14,axiom,(
% 6.88/1.55    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) <=> ~r2_hidden(X0,X1))),
% 6.88/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.88/1.55  
% 6.88/1.55  fof(f60,plain,(
% 6.88/1.55    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) | r2_hidden(X0,X1)) & (~r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)))),
% 6.88/1.55    inference(nnf_transformation,[],[f14])).
% 6.88/1.55  
% 6.88/1.55  fof(f82,plain,(
% 6.88/1.55    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)) )),
% 6.88/1.55    inference(cnf_transformation,[],[f60])).
% 6.88/1.55  
% 6.88/1.55  fof(f3,axiom,(
% 6.88/1.55    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 6.88/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.88/1.55  
% 6.88/1.55  fof(f71,plain,(
% 6.88/1.55    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 6.88/1.55    inference(cnf_transformation,[],[f3])).
% 6.88/1.55  
% 6.88/1.55  fof(f20,axiom,(
% 6.88/1.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 6.88/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.88/1.55  
% 6.88/1.55  fof(f89,plain,(
% 6.88/1.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 6.88/1.55    inference(cnf_transformation,[],[f20])).
% 6.88/1.55  
% 6.88/1.55  fof(f121,plain,(
% 6.88/1.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 6.88/1.55    inference(definition_unfolding,[],[f89,f120])).
% 6.88/1.55  
% 6.88/1.55  fof(f122,plain,(
% 6.88/1.55    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k4_xboole_0(X0,X1)) )),
% 6.88/1.55    inference(definition_unfolding,[],[f71,f121])).
% 6.88/1.55  
% 6.88/1.55  fof(f127,plain,(
% 6.88/1.55    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 6.88/1.55    inference(definition_unfolding,[],[f82,f122,f123,f123])).
% 6.88/1.55  
% 6.88/1.55  fof(f16,axiom,(
% 6.88/1.55    ! [X0] : k3_tarski(k1_tarski(X0)) = X0),
% 6.88/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.88/1.55  
% 6.88/1.55  fof(f85,plain,(
% 6.88/1.55    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 6.88/1.55    inference(cnf_transformation,[],[f16])).
% 6.88/1.55  
% 6.88/1.55  fof(f128,plain,(
% 6.88/1.55    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 6.88/1.55    inference(definition_unfolding,[],[f85,f123])).
% 6.88/1.55  
% 6.88/1.55  fof(f15,axiom,(
% 6.88/1.55    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 6.88/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.88/1.55  
% 6.88/1.55  fof(f84,plain,(
% 6.88/1.55    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 6.88/1.55    inference(cnf_transformation,[],[f15])).
% 6.88/1.55  
% 6.88/1.55  fof(f24,axiom,(
% 6.88/1.55    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 6.88/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.88/1.55  
% 6.88/1.55  fof(f94,plain,(
% 6.88/1.55    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 6.88/1.55    inference(cnf_transformation,[],[f24])).
% 6.88/1.55  
% 6.88/1.55  fof(f4,axiom,(
% 6.88/1.55    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 6.88/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.88/1.55  
% 6.88/1.55  fof(f72,plain,(
% 6.88/1.55    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 6.88/1.55    inference(cnf_transformation,[],[f4])).
% 6.88/1.55  
% 6.88/1.55  fof(f124,plain,(
% 6.88/1.55    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) )),
% 6.88/1.55    inference(definition_unfolding,[],[f72,f121])).
% 6.88/1.55  
% 6.88/1.55  fof(f5,axiom,(
% 6.88/1.55    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 6.88/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.88/1.55  
% 6.88/1.55  fof(f73,plain,(
% 6.88/1.55    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 6.88/1.55    inference(cnf_transformation,[],[f5])).
% 6.88/1.55  
% 6.88/1.55  fof(f1,axiom,(
% 6.88/1.55    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 6.88/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.88/1.55  
% 6.88/1.55  fof(f67,plain,(
% 6.88/1.55    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 6.88/1.55    inference(cnf_transformation,[],[f1])).
% 6.88/1.55  
% 6.88/1.55  cnf(c_2,plain,
% 6.88/1.55      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 6.88/1.55      inference(cnf_transformation,[],[f69]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_1590,plain,
% 6.88/1.55      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 6.88/1.55      | r1_tarski(X0,X1) = iProver_top ),
% 6.88/1.55      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_1,plain,
% 6.88/1.55      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 6.88/1.55      inference(cnf_transformation,[],[f70]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_1591,plain,
% 6.88/1.55      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 6.88/1.55      | r1_tarski(X0,X1) = iProver_top ),
% 6.88/1.55      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_2996,plain,
% 6.88/1.55      ( r1_tarski(X0,X0) = iProver_top ),
% 6.88/1.55      inference(superposition,[status(thm)],[c_1590,c_1591]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_26,plain,
% 6.88/1.55      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 6.88/1.55      inference(cnf_transformation,[],[f102]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_1579,plain,
% 6.88/1.55      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 6.88/1.55      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_37,negated_conjecture,
% 6.88/1.55      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) ),
% 6.88/1.55      inference(cnf_transformation,[],[f131]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_1575,plain,
% 6.88/1.55      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) = iProver_top ),
% 6.88/1.55      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_23,plain,
% 6.88/1.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.88/1.55      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 6.88/1.55      inference(cnf_transformation,[],[f99]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_1582,plain,
% 6.88/1.55      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 6.88/1.55      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 6.88/1.55      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_3232,plain,
% 6.88/1.55      ( k1_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4) = k1_relat_1(sK4) ),
% 6.88/1.55      inference(superposition,[status(thm)],[c_1575,c_1582]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_34,plain,
% 6.88/1.55      ( ~ v1_funct_2(X0,X1,X2)
% 6.88/1.55      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.88/1.55      | k1_relset_1(X1,X2,X0) = X1
% 6.88/1.55      | k1_xboole_0 = X2 ),
% 6.88/1.55      inference(cnf_transformation,[],[f105]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_38,negated_conjecture,
% 6.88/1.55      ( v1_funct_2(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) ),
% 6.88/1.55      inference(cnf_transformation,[],[f132]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_649,plain,
% 6.88/1.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.88/1.55      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != X1
% 6.88/1.55      | k1_relset_1(X1,X2,X0) = X1
% 6.88/1.55      | sK3 != X2
% 6.88/1.55      | sK4 != X0
% 6.88/1.55      | k1_xboole_0 = X2 ),
% 6.88/1.55      inference(resolution_lifted,[status(thm)],[c_34,c_38]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_650,plain,
% 6.88/1.55      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))
% 6.88/1.55      | k1_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 6.88/1.55      | k1_xboole_0 = sK3 ),
% 6.88/1.55      inference(unflattening,[status(thm)],[c_649]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_36,negated_conjecture,
% 6.88/1.55      ( k1_xboole_0 != sK3 ),
% 6.88/1.55      inference(cnf_transformation,[],[f114]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_652,plain,
% 6.88/1.55      ( k1_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 6.88/1.55      inference(global_propositional_subsumption,
% 6.88/1.55                [status(thm)],
% 6.88/1.55                [c_650,c_37,c_36]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_3240,plain,
% 6.88/1.55      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_relat_1(sK4) ),
% 6.88/1.55      inference(demodulation,[status(thm)],[c_3232,c_652]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_3795,plain,
% 6.88/1.55      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3))) = iProver_top ),
% 6.88/1.55      inference(demodulation,[status(thm)],[c_3240,c_1575]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_12,plain,
% 6.88/1.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 6.88/1.55      | ~ r2_hidden(X2,X0)
% 6.88/1.55      | r2_hidden(X2,X1) ),
% 6.88/1.55      inference(cnf_transformation,[],[f87]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_1586,plain,
% 6.88/1.55      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 6.88/1.55      | r2_hidden(X2,X0) != iProver_top
% 6.88/1.55      | r2_hidden(X2,X1) = iProver_top ),
% 6.88/1.55      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_4816,plain,
% 6.88/1.55      ( r2_hidden(X0,k2_zfmisc_1(k1_relat_1(sK4),sK3)) = iProver_top
% 6.88/1.55      | r2_hidden(X0,sK4) != iProver_top ),
% 6.88/1.55      inference(superposition,[status(thm)],[c_3795,c_1586]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_25,plain,
% 6.88/1.55      ( ~ r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2))
% 6.88/1.55      | k1_mcart_1(X0) = X1 ),
% 6.88/1.55      inference(cnf_transformation,[],[f130]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_1580,plain,
% 6.88/1.55      ( k1_mcart_1(X0) = X1
% 6.88/1.55      | r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)) != iProver_top ),
% 6.88/1.55      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_4661,plain,
% 6.88/1.55      ( k1_mcart_1(X0) = sK2
% 6.88/1.55      | r2_hidden(X0,k2_zfmisc_1(k1_relat_1(sK4),X1)) != iProver_top ),
% 6.88/1.55      inference(superposition,[status(thm)],[c_3240,c_1580]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_5665,plain,
% 6.88/1.55      ( k1_mcart_1(X0) = sK2 | r2_hidden(X0,sK4) != iProver_top ),
% 6.88/1.55      inference(superposition,[status(thm)],[c_4816,c_4661]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_6437,plain,
% 6.88/1.55      ( k1_mcart_1(sK1(sK4)) = sK2 | sK4 = k1_xboole_0 ),
% 6.88/1.55      inference(superposition,[status(thm)],[c_1579,c_5665]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_28,plain,
% 6.88/1.55      ( ~ r2_hidden(X0,X1)
% 6.88/1.55      | r2_hidden(k1_mcart_1(X0),k1_relat_1(X1))
% 6.88/1.55      | ~ v1_relat_1(X1) ),
% 6.88/1.55      inference(cnf_transformation,[],[f103]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_1577,plain,
% 6.88/1.55      ( r2_hidden(X0,X1) != iProver_top
% 6.88/1.55      | r2_hidden(k1_mcart_1(X0),k1_relat_1(X1)) = iProver_top
% 6.88/1.55      | v1_relat_1(X1) != iProver_top ),
% 6.88/1.55      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_7685,plain,
% 6.88/1.55      ( sK4 = k1_xboole_0
% 6.88/1.55      | r2_hidden(sK1(sK4),X0) != iProver_top
% 6.88/1.55      | r2_hidden(sK2,k1_relat_1(X0)) = iProver_top
% 6.88/1.55      | v1_relat_1(X0) != iProver_top ),
% 6.88/1.55      inference(superposition,[status(thm)],[c_6437,c_1577]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_17777,plain,
% 6.88/1.55      ( sK4 = k1_xboole_0
% 6.88/1.55      | r2_hidden(sK2,k1_relat_1(sK4)) = iProver_top
% 6.88/1.55      | v1_relat_1(sK4) != iProver_top ),
% 6.88/1.55      inference(superposition,[status(thm)],[c_1579,c_7685]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_42,plain,
% 6.88/1.55      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) = iProver_top ),
% 6.88/1.55      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_35,negated_conjecture,
% 6.88/1.55      ( ~ r2_hidden(k1_funct_1(sK4,sK2),sK3) ),
% 6.88/1.55      inference(cnf_transformation,[],[f115]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_43,plain,
% 6.88/1.55      ( r2_hidden(k1_funct_1(sK4,sK2),sK3) != iProver_top ),
% 6.88/1.55      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_21,plain,
% 6.88/1.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 6.88/1.55      inference(cnf_transformation,[],[f97]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_1774,plain,
% 6.88/1.55      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))
% 6.88/1.55      | v1_relat_1(sK4) ),
% 6.88/1.55      inference(instantiation,[status(thm)],[c_21]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_1775,plain,
% 6.88/1.55      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) != iProver_top
% 6.88/1.55      | v1_relat_1(sK4) = iProver_top ),
% 6.88/1.55      inference(predicate_to_equality,[status(thm)],[c_1774]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_22,plain,
% 6.88/1.55      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 6.88/1.55      inference(cnf_transformation,[],[f98]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_17,plain,
% 6.88/1.55      ( ~ v5_relat_1(X0,X1) | r1_tarski(k2_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 6.88/1.55      inference(cnf_transformation,[],[f92]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_479,plain,
% 6.88/1.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.88/1.55      | r1_tarski(k2_relat_1(X0),X2)
% 6.88/1.55      | ~ v1_relat_1(X0) ),
% 6.88/1.55      inference(resolution,[status(thm)],[c_22,c_17]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_483,plain,
% 6.88/1.55      ( r1_tarski(k2_relat_1(X0),X2)
% 6.88/1.55      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 6.88/1.55      inference(global_propositional_subsumption,[status(thm)],[c_479,c_21]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_484,plain,
% 6.88/1.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.88/1.55      | r1_tarski(k2_relat_1(X0),X2) ),
% 6.88/1.55      inference(renaming,[status(thm)],[c_483]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_1792,plain,
% 6.88/1.55      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))
% 6.88/1.55      | r1_tarski(k2_relat_1(sK4),sK3) ),
% 6.88/1.55      inference(instantiation,[status(thm)],[c_484]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_1793,plain,
% 6.88/1.55      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) != iProver_top
% 6.88/1.55      | r1_tarski(k2_relat_1(sK4),sK3) = iProver_top ),
% 6.88/1.55      inference(predicate_to_equality,[status(thm)],[c_1792]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_3,plain,
% 6.88/1.55      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 6.88/1.55      inference(cnf_transformation,[],[f68]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_1780,plain,
% 6.88/1.55      ( ~ r2_hidden(k1_funct_1(sK4,sK2),X0)
% 6.88/1.55      | r2_hidden(k1_funct_1(sK4,sK2),sK3)
% 6.88/1.55      | ~ r1_tarski(X0,sK3) ),
% 6.88/1.55      inference(instantiation,[status(thm)],[c_3]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_1903,plain,
% 6.88/1.55      ( ~ r2_hidden(k1_funct_1(sK4,sK2),k2_relat_1(sK4))
% 6.88/1.55      | r2_hidden(k1_funct_1(sK4,sK2),sK3)
% 6.88/1.55      | ~ r1_tarski(k2_relat_1(sK4),sK3) ),
% 6.88/1.55      inference(instantiation,[status(thm)],[c_1780]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_1904,plain,
% 6.88/1.55      ( r2_hidden(k1_funct_1(sK4,sK2),k2_relat_1(sK4)) != iProver_top
% 6.88/1.55      | r2_hidden(k1_funct_1(sK4,sK2),sK3) = iProver_top
% 6.88/1.55      | r1_tarski(k2_relat_1(sK4),sK3) != iProver_top ),
% 6.88/1.55      inference(predicate_to_equality,[status(thm)],[c_1903]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_20,plain,
% 6.88/1.55      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 6.88/1.55      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 6.88/1.55      | ~ v1_funct_1(X1)
% 6.88/1.55      | ~ v1_relat_1(X1) ),
% 6.88/1.55      inference(cnf_transformation,[],[f96]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_39,negated_conjecture,
% 6.88/1.55      ( v1_funct_1(sK4) ),
% 6.88/1.55      inference(cnf_transformation,[],[f111]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_460,plain,
% 6.88/1.55      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 6.88/1.55      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 6.88/1.55      | ~ v1_relat_1(X1)
% 6.88/1.55      | sK4 != X1 ),
% 6.88/1.55      inference(resolution_lifted,[status(thm)],[c_20,c_39]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_461,plain,
% 6.88/1.55      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 6.88/1.55      | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4))
% 6.88/1.55      | ~ v1_relat_1(sK4) ),
% 6.88/1.55      inference(unflattening,[status(thm)],[c_460]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_2272,plain,
% 6.88/1.55      ( r2_hidden(k1_funct_1(sK4,sK2),k2_relat_1(sK4))
% 6.88/1.55      | ~ r2_hidden(sK2,k1_relat_1(sK4))
% 6.88/1.55      | ~ v1_relat_1(sK4) ),
% 6.88/1.55      inference(instantiation,[status(thm)],[c_461]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_2275,plain,
% 6.88/1.55      ( r2_hidden(k1_funct_1(sK4,sK2),k2_relat_1(sK4)) = iProver_top
% 6.88/1.55      | r2_hidden(sK2,k1_relat_1(sK4)) != iProver_top
% 6.88/1.55      | v1_relat_1(sK4) != iProver_top ),
% 6.88/1.55      inference(predicate_to_equality,[status(thm)],[c_2272]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_17819,plain,
% 6.88/1.55      ( sK4 = k1_xboole_0 ),
% 6.88/1.55      inference(global_propositional_subsumption,
% 6.88/1.55                [status(thm)],
% 6.88/1.55                [c_17777,c_42,c_43,c_1775,c_1793,c_1904,c_2275]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_11,plain,
% 6.88/1.55      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 6.88/1.55      inference(cnf_transformation,[],[f86]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_14,plain,
% 6.88/1.55      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 6.88/1.55      inference(cnf_transformation,[],[f90]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_445,plain,
% 6.88/1.55      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | k1_zfmisc_1(X2) != X1 ),
% 6.88/1.55      inference(resolution_lifted,[status(thm)],[c_11,c_14]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_446,plain,
% 6.88/1.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 6.88/1.55      inference(unflattening,[status(thm)],[c_445]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_1574,plain,
% 6.88/1.55      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 6.88/1.55      | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
% 6.88/1.55      inference(predicate_to_equality,[status(thm)],[c_446]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_2316,plain,
% 6.88/1.55      ( r2_hidden(sK4,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) = iProver_top ),
% 6.88/1.55      inference(superposition,[status(thm)],[c_1575,c_1574]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_3793,plain,
% 6.88/1.55      ( r2_hidden(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3))) = iProver_top ),
% 6.88/1.55      inference(demodulation,[status(thm)],[c_3240,c_2316]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_1589,plain,
% 6.88/1.55      ( r2_hidden(X0,X1) != iProver_top
% 6.88/1.55      | r2_hidden(X0,X2) = iProver_top
% 6.88/1.55      | r1_tarski(X1,X2) != iProver_top ),
% 6.88/1.55      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_4326,plain,
% 6.88/1.55      ( r2_hidden(sK4,X0) = iProver_top
% 6.88/1.55      | r1_tarski(k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3)),X0) != iProver_top ),
% 6.88/1.55      inference(superposition,[status(thm)],[c_3793,c_1589]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_17882,plain,
% 6.88/1.55      ( r2_hidden(k1_xboole_0,X0) = iProver_top
% 6.88/1.55      | r1_tarski(k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),sK3)),X0) != iProver_top ),
% 6.88/1.55      inference(demodulation,[status(thm)],[c_17819,c_4326]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_6,plain,
% 6.88/1.55      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
% 6.88/1.55      inference(cnf_transformation,[],[f125]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_8,plain,
% 6.88/1.55      ( ~ r2_hidden(X0,X1)
% 6.88/1.55      | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 6.88/1.55      inference(cnf_transformation,[],[f127]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_1587,plain,
% 6.88/1.55      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
% 6.88/1.55      | r2_hidden(X0,X1) != iProver_top ),
% 6.88/1.55      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_6027,plain,
% 6.88/1.55      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
% 6.88/1.55      | r2_hidden(X0,X1) != iProver_top ),
% 6.88/1.55      inference(superposition,[status(thm)],[c_6,c_1587]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_6144,plain,
% 6.88/1.55      ( k5_xboole_0(k1_relat_1(sK4),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_relat_1(sK4)))) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 6.88/1.55      | r2_hidden(sK2,X0) != iProver_top ),
% 6.88/1.55      inference(superposition,[status(thm)],[c_3240,c_6027]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_6147,plain,
% 6.88/1.55      ( k5_xboole_0(k1_relat_1(sK4),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_relat_1(sK4)))) != k1_relat_1(sK4)
% 6.88/1.55      | r2_hidden(sK2,X0) != iProver_top ),
% 6.88/1.55      inference(light_normalisation,[status(thm)],[c_6144,c_3240]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_17887,plain,
% 6.88/1.55      ( k5_xboole_0(k1_relat_1(k1_xboole_0),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_relat_1(k1_xboole_0)))) != k1_relat_1(k1_xboole_0)
% 6.88/1.55      | r2_hidden(sK2,X0) != iProver_top ),
% 6.88/1.55      inference(demodulation,[status(thm)],[c_17819,c_6147]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_10,plain,
% 6.88/1.55      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 6.88/1.55      inference(cnf_transformation,[],[f128]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_3811,plain,
% 6.88/1.55      ( k3_tarski(k1_relat_1(sK4)) = sK2 ),
% 6.88/1.55      inference(superposition,[status(thm)],[c_3240,c_10]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_17900,plain,
% 6.88/1.55      ( k3_tarski(k1_relat_1(k1_xboole_0)) = sK2 ),
% 6.88/1.55      inference(demodulation,[status(thm)],[c_17819,c_3811]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_9,plain,
% 6.88/1.55      ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
% 6.88/1.55      inference(cnf_transformation,[],[f84]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_19,plain,
% 6.88/1.55      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 6.88/1.55      inference(cnf_transformation,[],[f94]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_17920,plain,
% 6.88/1.55      ( sK2 = k1_xboole_0 ),
% 6.88/1.55      inference(light_normalisation,[status(thm)],[c_17900,c_9,c_19]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_17965,plain,
% 6.88/1.55      ( k5_xboole_0(k1_relat_1(k1_xboole_0),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_relat_1(k1_xboole_0)))) != k1_relat_1(k1_xboole_0)
% 6.88/1.55      | r2_hidden(k1_xboole_0,X0) != iProver_top ),
% 6.88/1.55      inference(light_normalisation,[status(thm)],[c_17887,c_17920]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_4,plain,
% 6.88/1.55      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
% 6.88/1.55      inference(cnf_transformation,[],[f124]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_17968,plain,
% 6.88/1.55      ( k5_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 6.88/1.55      | r2_hidden(k1_xboole_0,X0) != iProver_top ),
% 6.88/1.55      inference(light_normalisation,[status(thm)],[c_17965,c_4,c_19]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_5,plain,
% 6.88/1.55      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 6.88/1.55      inference(cnf_transformation,[],[f73]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_0,plain,
% 6.88/1.55      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 6.88/1.55      inference(cnf_transformation,[],[f67]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_1962,plain,
% 6.88/1.55      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 6.88/1.55      inference(superposition,[status(thm)],[c_5,c_0]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_17969,plain,
% 6.88/1.55      ( k1_xboole_0 != k1_xboole_0 | r2_hidden(k1_xboole_0,X0) != iProver_top ),
% 6.88/1.55      inference(demodulation,[status(thm)],[c_17968,c_1962]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_17970,plain,
% 6.88/1.55      ( r2_hidden(k1_xboole_0,X0) != iProver_top ),
% 6.88/1.55      inference(equality_resolution_simp,[status(thm)],[c_17969]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_17978,plain,
% 6.88/1.55      ( r1_tarski(k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),sK3)),X0) != iProver_top ),
% 6.88/1.55      inference(forward_subsumption_resolution,[status(thm)],[c_17882,c_17970]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_17979,plain,
% 6.88/1.55      ( r1_tarski(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)),X0) != iProver_top ),
% 6.88/1.55      inference(light_normalisation,[status(thm)],[c_17978,c_19]) ).
% 6.88/1.55  
% 6.88/1.55  cnf(c_19763,plain,
% 6.88/1.55      ( $false ),
% 6.88/1.55      inference(superposition,[status(thm)],[c_2996,c_17979]) ).
% 6.88/1.55  
% 6.88/1.55  
% 6.88/1.55  % SZS output end CNFRefutation for theBenchmark.p
% 6.88/1.55  
% 6.88/1.55  ------                               Statistics
% 6.88/1.55  
% 6.88/1.55  ------ General
% 6.88/1.55  
% 6.88/1.55  abstr_ref_over_cycles:                  0
% 6.88/1.55  abstr_ref_under_cycles:                 0
% 6.88/1.55  gc_basic_clause_elim:                   0
% 6.88/1.55  forced_gc_time:                         0
% 6.88/1.55  parsing_time:                           0.038
% 6.88/1.55  unif_index_cands_time:                  0.
% 6.88/1.55  unif_index_add_time:                    0.
% 6.88/1.55  orderings_time:                         0.
% 6.88/1.55  out_proof_time:                         0.01
% 6.88/1.55  total_time:                             0.636
% 6.88/1.55  num_of_symbols:                         57
% 6.88/1.55  num_of_terms:                           12088
% 6.88/1.55  
% 6.88/1.55  ------ Preprocessing
% 6.88/1.55  
% 6.88/1.55  num_of_splits:                          0
% 6.88/1.55  num_of_split_atoms:                     0
% 6.88/1.55  num_of_reused_defs:                     0
% 6.88/1.55  num_eq_ax_congr_red:                    23
% 6.88/1.55  num_of_sem_filtered_clauses:            1
% 6.88/1.55  num_of_subtypes:                        0
% 6.88/1.55  monotx_restored_types:                  0
% 6.88/1.55  sat_num_of_epr_types:                   0
% 6.88/1.55  sat_num_of_non_cyclic_types:            0
% 6.88/1.55  sat_guarded_non_collapsed_types:        0
% 6.88/1.55  num_pure_diseq_elim:                    0
% 6.88/1.55  simp_replaced_by:                       0
% 6.88/1.55  res_preprocessed:                       169
% 6.88/1.55  prep_upred:                             0
% 6.88/1.55  prep_unflattend:                        47
% 6.88/1.55  smt_new_axioms:                         0
% 6.88/1.55  pred_elim_cands:                        4
% 6.88/1.55  pred_elim:                              4
% 6.88/1.55  pred_elim_cl:                           8
% 6.88/1.55  pred_elim_cycles:                       9
% 6.88/1.55  merged_defs:                            8
% 6.88/1.55  merged_defs_ncl:                        0
% 6.88/1.55  bin_hyper_res:                          8
% 6.88/1.55  prep_cycles:                            4
% 6.88/1.55  pred_elim_time:                         0.012
% 6.88/1.55  splitting_time:                         0.
% 6.88/1.55  sem_filter_time:                        0.
% 6.88/1.55  monotx_time:                            0.
% 6.88/1.55  subtype_inf_time:                       0.
% 6.88/1.55  
% 6.88/1.55  ------ Problem properties
% 6.88/1.55  
% 6.88/1.55  clauses:                                32
% 6.88/1.55  conjectures:                            3
% 6.88/1.55  epr:                                    2
% 6.88/1.55  horn:                                   28
% 6.88/1.55  ground:                                 9
% 6.88/1.55  unary:                                  13
% 6.88/1.55  binary:                                 11
% 6.88/1.55  lits:                                   60
% 6.88/1.55  lits_eq:                                20
% 6.88/1.55  fd_pure:                                0
% 6.88/1.55  fd_pseudo:                              0
% 6.88/1.55  fd_cond:                                1
% 6.88/1.55  fd_pseudo_cond:                         1
% 6.88/1.55  ac_symbols:                             0
% 6.88/1.55  
% 6.88/1.55  ------ Propositional Solver
% 6.88/1.55  
% 6.88/1.55  prop_solver_calls:                      29
% 6.88/1.55  prop_fast_solver_calls:                 1181
% 6.88/1.55  smt_solver_calls:                       0
% 6.88/1.55  smt_fast_solver_calls:                  0
% 6.88/1.55  prop_num_of_clauses:                    6571
% 6.88/1.55  prop_preprocess_simplified:             12677
% 6.88/1.55  prop_fo_subsumed:                       17
% 6.88/1.55  prop_solver_time:                       0.
% 6.88/1.55  smt_solver_time:                        0.
% 6.88/1.55  smt_fast_solver_time:                   0.
% 6.88/1.55  prop_fast_solver_time:                  0.
% 6.88/1.55  prop_unsat_core_time:                   0.
% 6.88/1.55  
% 6.88/1.55  ------ QBF
% 6.88/1.55  
% 6.88/1.55  qbf_q_res:                              0
% 6.88/1.55  qbf_num_tautologies:                    0
% 6.88/1.55  qbf_prep_cycles:                        0
% 6.88/1.55  
% 6.88/1.55  ------ BMC1
% 6.88/1.55  
% 6.88/1.55  bmc1_current_bound:                     -1
% 6.88/1.55  bmc1_last_solved_bound:                 -1
% 6.88/1.55  bmc1_unsat_core_size:                   -1
% 6.88/1.55  bmc1_unsat_core_parents_size:           -1
% 6.88/1.55  bmc1_merge_next_fun:                    0
% 6.88/1.55  bmc1_unsat_core_clauses_time:           0.
% 6.88/1.55  
% 6.88/1.55  ------ Instantiation
% 6.88/1.55  
% 6.88/1.55  inst_num_of_clauses:                    1602
% 6.88/1.55  inst_num_in_passive:                    238
% 6.88/1.55  inst_num_in_active:                     613
% 6.88/1.55  inst_num_in_unprocessed:                751
% 6.88/1.55  inst_num_of_loops:                      740
% 6.88/1.55  inst_num_of_learning_restarts:          0
% 6.88/1.55  inst_num_moves_active_passive:          124
% 6.88/1.55  inst_lit_activity:                      0
% 6.88/1.55  inst_lit_activity_moves:                0
% 6.88/1.55  inst_num_tautologies:                   0
% 6.88/1.55  inst_num_prop_implied:                  0
% 6.88/1.55  inst_num_existing_simplified:           0
% 6.88/1.55  inst_num_eq_res_simplified:             0
% 6.88/1.55  inst_num_child_elim:                    0
% 6.88/1.55  inst_num_of_dismatching_blockings:      1245
% 6.88/1.55  inst_num_of_non_proper_insts:           1706
% 6.88/1.55  inst_num_of_duplicates:                 0
% 6.88/1.55  inst_inst_num_from_inst_to_res:         0
% 6.88/1.55  inst_dismatching_checking_time:         0.
% 6.88/1.55  
% 6.88/1.55  ------ Resolution
% 6.88/1.55  
% 6.88/1.55  res_num_of_clauses:                     0
% 6.88/1.55  res_num_in_passive:                     0
% 6.88/1.55  res_num_in_active:                      0
% 6.88/1.55  res_num_of_loops:                       173
% 6.88/1.55  res_forward_subset_subsumed:            97
% 6.88/1.55  res_backward_subset_subsumed:           0
% 6.88/1.55  res_forward_subsumed:                   0
% 6.88/1.55  res_backward_subsumed:                  0
% 6.88/1.55  res_forward_subsumption_resolution:     0
% 6.88/1.55  res_backward_subsumption_resolution:    0
% 6.88/1.55  res_clause_to_clause_subsumption:       2019
% 6.88/1.55  res_orphan_elimination:                 0
% 6.88/1.55  res_tautology_del:                      168
% 6.88/1.55  res_num_eq_res_simplified:              0
% 6.88/1.55  res_num_sel_changes:                    0
% 6.88/1.55  res_moves_from_active_to_pass:          0
% 6.88/1.55  
% 6.88/1.55  ------ Superposition
% 6.88/1.55  
% 6.88/1.55  sup_time_total:                         0.
% 6.88/1.55  sup_time_generating:                    0.
% 6.88/1.55  sup_time_sim_full:                      0.
% 6.88/1.55  sup_time_sim_immed:                     0.
% 6.88/1.55  
% 6.88/1.55  sup_num_of_clauses:                     342
% 6.88/1.55  sup_num_in_active:                      50
% 6.88/1.55  sup_num_in_passive:                     292
% 6.88/1.55  sup_num_of_loops:                       146
% 6.88/1.55  sup_fw_superposition:                   353
% 6.88/1.55  sup_bw_superposition:                   141
% 6.88/1.55  sup_immediate_simplified:               164
% 6.88/1.55  sup_given_eliminated:                   0
% 6.88/1.55  comparisons_done:                       0
% 6.88/1.55  comparisons_avoided:                    18
% 6.88/1.55  
% 6.88/1.55  ------ Simplifications
% 6.88/1.55  
% 6.88/1.55  
% 6.88/1.55  sim_fw_subset_subsumed:                 21
% 6.88/1.55  sim_bw_subset_subsumed:                 9
% 6.88/1.55  sim_fw_subsumed:                        65
% 6.88/1.55  sim_bw_subsumed:                        21
% 6.88/1.55  sim_fw_subsumption_res:                 1
% 6.88/1.55  sim_bw_subsumption_res:                 0
% 6.88/1.55  sim_tautology_del:                      1
% 6.88/1.55  sim_eq_tautology_del:                   7
% 6.88/1.55  sim_eq_res_simp:                        4
% 6.88/1.55  sim_fw_demodulated:                     6
% 6.88/1.55  sim_bw_demodulated:                     95
% 6.88/1.55  sim_light_normalised:                   113
% 6.88/1.55  sim_joinable_taut:                      0
% 6.88/1.55  sim_joinable_simp:                      0
% 6.88/1.55  sim_ac_normalised:                      0
% 6.88/1.55  sim_smt_subsumption:                    0
% 6.88/1.55  
%------------------------------------------------------------------------------
