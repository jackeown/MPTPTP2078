%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:04:58 EST 2020

% Result     : Theorem 3.34s
% Output     : CNFRefutation 3.34s
% Verified   : 
% Statistics : Number of formulae       :  158 (1062 expanded)
%              Number of clauses        :   64 ( 143 expanded)
%              Number of leaves         :   28 ( 294 expanded)
%              Depth                    :   27
%              Number of atoms          :  398 (2460 expanded)
%              Number of equality atoms :  197 (1220 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
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
    inference(nnf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f44])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f116,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f56])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f46])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK1(X0,X1),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( r1_tarski(sK1(X0,X1),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK1(X0,X1),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r1_tarski(sK1(X0,X1),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f47,f48])).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f117,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f71])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f42])).

fof(f55,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f27,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f40,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f41,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f52,plain,
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

fof(f53,plain,
    ( ~ r2_hidden(k1_funct_1(sK4,sK2),sK3)
    & k1_xboole_0 != sK3
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))
    & v1_funct_2(sK4,k1_tarski(sK2),sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f41,f52])).

fof(f96,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) ),
    inference(cnf_transformation,[],[f53])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f14])).

fof(f99,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f68,f69])).

fof(f100,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f67,f99])).

fof(f101,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f66,f100])).

fof(f102,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f65,f101])).

fof(f103,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f64,f102])).

fof(f106,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f63,f103])).

fof(f113,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) ),
    inference(definition_unfolding,[],[f96,f106])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f25,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f25])).

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
    inference(flattening,[],[f36])).

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
    inference(nnf_transformation,[],[f37])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f95,plain,(
    v1_funct_2(sK4,k1_tarski(sK2),sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f114,plain,(
    v1_funct_2(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) ),
    inference(definition_unfolding,[],[f95,f106])).

fof(f97,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f53])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 )
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k1_mcart_1(X0) = X1
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( k1_mcart_1(X0) = X1
      | ~ r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)) ) ),
    inference(definition_unfolding,[],[f85,f106])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f26,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f38])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f94,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f98,plain,(
    ~ r2_hidden(k1_funct_1(sK4,sK2),sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f108,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f62,f103,f103])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
        | r2_hidden(X0,X1) )
      & ( ~ r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f19,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f104,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f78,f103])).

fof(f105,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f59,f104])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f74,f105,f106,f106])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f107,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f60,f104])).

fof(f21,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_1421,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_1418,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1423,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_1405,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1411,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2742,plain,
    ( k1_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1405,c_1411])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_509,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != X1
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X2
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_34])).

cnf(c_510,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))
    | k1_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_509])).

cnf(c_32,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_512,plain,
    ( k1_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_510,c_33,c_32])).

cnf(c_2750,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_2742,c_512])).

cnf(c_2939,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2750,c_1405])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1414,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3679,plain,
    ( r2_hidden(X0,k2_zfmisc_1(k1_relat_1(sK4),sK3)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2939,c_1414])).

cnf(c_23,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2))
    | k1_mcart_1(X0) = X1 ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1407,plain,
    ( k1_mcart_1(X0) = X1
    | r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2959,plain,
    ( k1_mcart_1(X0) = sK2
    | r2_hidden(X0,k2_zfmisc_1(k1_relat_1(sK4),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2750,c_1407])).

cnf(c_4094,plain,
    ( k1_mcart_1(X0) = sK2
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3679,c_2959])).

cnf(c_4202,plain,
    ( k1_mcart_1(sK0(sK4)) = sK2
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1423,c_4094])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k1_mcart_1(X0),X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1409,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4093,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(k1_mcart_1(X0),k1_relat_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3679,c_1409])).

cnf(c_5653,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK0(sK4),sK4) != iProver_top
    | r2_hidden(sK2,k1_relat_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4202,c_4093])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_414,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_35])).

cnf(c_415,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(k1_funct_1(sK4,X2),X1)
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_414])).

cnf(c_536,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(k1_funct_1(sK4,X2),X1)
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != X0
    | sK3 != X1
    | sK4 != sK4
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_415])).

cnf(c_537,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))
    | ~ r2_hidden(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | r2_hidden(k1_funct_1(sK4,X0),sK3)
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_536])).

cnf(c_541,plain,
    ( r2_hidden(k1_funct_1(sK4,X0),sK3)
    | ~ r2_hidden(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_537,c_33,c_32])).

cnf(c_542,plain,
    ( ~ r2_hidden(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | r2_hidden(k1_funct_1(sK4,X0),sK3) ),
    inference(renaming,[status(thm)],[c_541])).

cnf(c_1401,plain,
    ( r2_hidden(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_542])).

cnf(c_2938,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2750,c_1401])).

cnf(c_31,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(sK4,sK2),sK3) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1406,plain,
    ( r2_hidden(k1_funct_1(sK4,sK2),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3181,plain,
    ( r2_hidden(sK2,k1_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2938,c_1406])).

cnf(c_6035,plain,
    ( r2_hidden(sK0(sK4),sK4) != iProver_top
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5653,c_3181])).

cnf(c_6036,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK0(sK4),sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_6035])).

cnf(c_6041,plain,
    ( sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1423,c_6036])).

cnf(c_7,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1415,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4594,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
    | r2_hidden(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_1415])).

cnf(c_4762,plain,
    ( k5_xboole_0(k1_relat_1(sK4),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_relat_1(sK4)))) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | r2_hidden(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2750,c_4594])).

cnf(c_4765,plain,
    ( k5_xboole_0(k1_relat_1(sK4),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_relat_1(sK4)))) != k1_relat_1(sK4)
    | r2_hidden(sK2,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4762,c_2750])).

cnf(c_6967,plain,
    ( k5_xboole_0(k1_relat_1(k1_xboole_0),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_relat_1(k1_xboole_0)))) != k1_relat_1(k1_xboole_0)
    | r2_hidden(sK2,X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6041,c_4765])).

cnf(c_5,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_18,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_7042,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | r2_hidden(sK2,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6967,c_5,c_18])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1926,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_6,c_0])).

cnf(c_7043,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(sK2,X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7042,c_1926])).

cnf(c_7044,plain,
    ( r2_hidden(sK2,X0) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_7043])).

cnf(c_9020,plain,
    ( r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1418,c_7044])).

cnf(c_9031,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_1421,c_9020])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:44:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 3.34/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/1.02  
% 3.34/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.34/1.02  
% 3.34/1.02  ------  iProver source info
% 3.34/1.02  
% 3.34/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.34/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.34/1.02  git: non_committed_changes: false
% 3.34/1.02  git: last_make_outside_of_git: false
% 3.34/1.02  
% 3.34/1.02  ------ 
% 3.34/1.02  
% 3.34/1.02  ------ Input Options
% 3.34/1.02  
% 3.34/1.02  --out_options                           all
% 3.34/1.02  --tptp_safe_out                         true
% 3.34/1.02  --problem_path                          ""
% 3.34/1.02  --include_path                          ""
% 3.34/1.02  --clausifier                            res/vclausify_rel
% 3.34/1.02  --clausifier_options                    --mode clausify
% 3.34/1.02  --stdin                                 false
% 3.34/1.02  --stats_out                             all
% 3.34/1.02  
% 3.34/1.02  ------ General Options
% 3.34/1.02  
% 3.34/1.02  --fof                                   false
% 3.34/1.02  --time_out_real                         305.
% 3.34/1.02  --time_out_virtual                      -1.
% 3.34/1.02  --symbol_type_check                     false
% 3.34/1.02  --clausify_out                          false
% 3.34/1.02  --sig_cnt_out                           false
% 3.34/1.02  --trig_cnt_out                          false
% 3.34/1.02  --trig_cnt_out_tolerance                1.
% 3.34/1.02  --trig_cnt_out_sk_spl                   false
% 3.34/1.02  --abstr_cl_out                          false
% 3.34/1.02  
% 3.34/1.02  ------ Global Options
% 3.34/1.02  
% 3.34/1.02  --schedule                              default
% 3.34/1.02  --add_important_lit                     false
% 3.34/1.02  --prop_solver_per_cl                    1000
% 3.34/1.02  --min_unsat_core                        false
% 3.34/1.02  --soft_assumptions                      false
% 3.34/1.02  --soft_lemma_size                       3
% 3.34/1.02  --prop_impl_unit_size                   0
% 3.34/1.02  --prop_impl_unit                        []
% 3.34/1.02  --share_sel_clauses                     true
% 3.34/1.02  --reset_solvers                         false
% 3.34/1.02  --bc_imp_inh                            [conj_cone]
% 3.34/1.02  --conj_cone_tolerance                   3.
% 3.34/1.02  --extra_neg_conj                        none
% 3.34/1.02  --large_theory_mode                     true
% 3.34/1.02  --prolific_symb_bound                   200
% 3.34/1.02  --lt_threshold                          2000
% 3.34/1.02  --clause_weak_htbl                      true
% 3.34/1.02  --gc_record_bc_elim                     false
% 3.34/1.02  
% 3.34/1.02  ------ Preprocessing Options
% 3.34/1.02  
% 3.34/1.02  --preprocessing_flag                    true
% 3.34/1.02  --time_out_prep_mult                    0.1
% 3.34/1.02  --splitting_mode                        input
% 3.34/1.02  --splitting_grd                         true
% 3.34/1.02  --splitting_cvd                         false
% 3.34/1.02  --splitting_cvd_svl                     false
% 3.34/1.02  --splitting_nvd                         32
% 3.34/1.02  --sub_typing                            true
% 3.34/1.02  --prep_gs_sim                           true
% 3.34/1.02  --prep_unflatten                        true
% 3.34/1.02  --prep_res_sim                          true
% 3.34/1.02  --prep_upred                            true
% 3.34/1.02  --prep_sem_filter                       exhaustive
% 3.34/1.02  --prep_sem_filter_out                   false
% 3.34/1.02  --pred_elim                             true
% 3.34/1.02  --res_sim_input                         true
% 3.34/1.02  --eq_ax_congr_red                       true
% 3.34/1.02  --pure_diseq_elim                       true
% 3.34/1.02  --brand_transform                       false
% 3.34/1.02  --non_eq_to_eq                          false
% 3.34/1.02  --prep_def_merge                        true
% 3.34/1.02  --prep_def_merge_prop_impl              false
% 3.34/1.02  --prep_def_merge_mbd                    true
% 3.34/1.02  --prep_def_merge_tr_red                 false
% 3.34/1.02  --prep_def_merge_tr_cl                  false
% 3.34/1.02  --smt_preprocessing                     true
% 3.34/1.02  --smt_ac_axioms                         fast
% 3.34/1.02  --preprocessed_out                      false
% 3.34/1.02  --preprocessed_stats                    false
% 3.34/1.02  
% 3.34/1.02  ------ Abstraction refinement Options
% 3.34/1.02  
% 3.34/1.02  --abstr_ref                             []
% 3.34/1.02  --abstr_ref_prep                        false
% 3.34/1.02  --abstr_ref_until_sat                   false
% 3.34/1.02  --abstr_ref_sig_restrict                funpre
% 3.34/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.34/1.02  --abstr_ref_under                       []
% 3.34/1.02  
% 3.34/1.02  ------ SAT Options
% 3.34/1.02  
% 3.34/1.02  --sat_mode                              false
% 3.34/1.02  --sat_fm_restart_options                ""
% 3.34/1.02  --sat_gr_def                            false
% 3.34/1.02  --sat_epr_types                         true
% 3.34/1.02  --sat_non_cyclic_types                  false
% 3.34/1.02  --sat_finite_models                     false
% 3.34/1.02  --sat_fm_lemmas                         false
% 3.34/1.02  --sat_fm_prep                           false
% 3.34/1.02  --sat_fm_uc_incr                        true
% 3.34/1.02  --sat_out_model                         small
% 3.34/1.02  --sat_out_clauses                       false
% 3.34/1.02  
% 3.34/1.02  ------ QBF Options
% 3.34/1.02  
% 3.34/1.02  --qbf_mode                              false
% 3.34/1.02  --qbf_elim_univ                         false
% 3.34/1.02  --qbf_dom_inst                          none
% 3.34/1.02  --qbf_dom_pre_inst                      false
% 3.34/1.02  --qbf_sk_in                             false
% 3.34/1.02  --qbf_pred_elim                         true
% 3.34/1.02  --qbf_split                             512
% 3.34/1.02  
% 3.34/1.02  ------ BMC1 Options
% 3.34/1.02  
% 3.34/1.02  --bmc1_incremental                      false
% 3.34/1.02  --bmc1_axioms                           reachable_all
% 3.34/1.02  --bmc1_min_bound                        0
% 3.34/1.02  --bmc1_max_bound                        -1
% 3.34/1.02  --bmc1_max_bound_default                -1
% 3.34/1.02  --bmc1_symbol_reachability              true
% 3.34/1.02  --bmc1_property_lemmas                  false
% 3.34/1.02  --bmc1_k_induction                      false
% 3.34/1.02  --bmc1_non_equiv_states                 false
% 3.34/1.02  --bmc1_deadlock                         false
% 3.34/1.02  --bmc1_ucm                              false
% 3.34/1.02  --bmc1_add_unsat_core                   none
% 3.34/1.02  --bmc1_unsat_core_children              false
% 3.34/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.34/1.02  --bmc1_out_stat                         full
% 3.34/1.02  --bmc1_ground_init                      false
% 3.34/1.02  --bmc1_pre_inst_next_state              false
% 3.34/1.02  --bmc1_pre_inst_state                   false
% 3.34/1.02  --bmc1_pre_inst_reach_state             false
% 3.34/1.02  --bmc1_out_unsat_core                   false
% 3.34/1.02  --bmc1_aig_witness_out                  false
% 3.34/1.02  --bmc1_verbose                          false
% 3.34/1.02  --bmc1_dump_clauses_tptp                false
% 3.34/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.34/1.02  --bmc1_dump_file                        -
% 3.34/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.34/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.34/1.02  --bmc1_ucm_extend_mode                  1
% 3.34/1.02  --bmc1_ucm_init_mode                    2
% 3.34/1.02  --bmc1_ucm_cone_mode                    none
% 3.34/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.34/1.02  --bmc1_ucm_relax_model                  4
% 3.34/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.34/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.34/1.02  --bmc1_ucm_layered_model                none
% 3.34/1.02  --bmc1_ucm_max_lemma_size               10
% 3.34/1.02  
% 3.34/1.02  ------ AIG Options
% 3.34/1.02  
% 3.34/1.02  --aig_mode                              false
% 3.34/1.02  
% 3.34/1.02  ------ Instantiation Options
% 3.34/1.02  
% 3.34/1.02  --instantiation_flag                    true
% 3.34/1.02  --inst_sos_flag                         false
% 3.34/1.02  --inst_sos_phase                        true
% 3.34/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.34/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.34/1.02  --inst_lit_sel_side                     num_symb
% 3.34/1.02  --inst_solver_per_active                1400
% 3.34/1.02  --inst_solver_calls_frac                1.
% 3.34/1.02  --inst_passive_queue_type               priority_queues
% 3.34/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.34/1.02  --inst_passive_queues_freq              [25;2]
% 3.34/1.02  --inst_dismatching                      true
% 3.34/1.02  --inst_eager_unprocessed_to_passive     true
% 3.34/1.02  --inst_prop_sim_given                   true
% 3.34/1.02  --inst_prop_sim_new                     false
% 3.34/1.02  --inst_subs_new                         false
% 3.34/1.02  --inst_eq_res_simp                      false
% 3.34/1.02  --inst_subs_given                       false
% 3.34/1.02  --inst_orphan_elimination               true
% 3.34/1.02  --inst_learning_loop_flag               true
% 3.34/1.02  --inst_learning_start                   3000
% 3.34/1.02  --inst_learning_factor                  2
% 3.34/1.02  --inst_start_prop_sim_after_learn       3
% 3.34/1.02  --inst_sel_renew                        solver
% 3.34/1.02  --inst_lit_activity_flag                true
% 3.34/1.02  --inst_restr_to_given                   false
% 3.34/1.02  --inst_activity_threshold               500
% 3.34/1.02  --inst_out_proof                        true
% 3.34/1.02  
% 3.34/1.02  ------ Resolution Options
% 3.34/1.02  
% 3.34/1.02  --resolution_flag                       true
% 3.34/1.02  --res_lit_sel                           adaptive
% 3.34/1.02  --res_lit_sel_side                      none
% 3.34/1.02  --res_ordering                          kbo
% 3.34/1.02  --res_to_prop_solver                    active
% 3.34/1.02  --res_prop_simpl_new                    false
% 3.34/1.02  --res_prop_simpl_given                  true
% 3.34/1.02  --res_passive_queue_type                priority_queues
% 3.34/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.34/1.02  --res_passive_queues_freq               [15;5]
% 3.34/1.02  --res_forward_subs                      full
% 3.34/1.02  --res_backward_subs                     full
% 3.34/1.02  --res_forward_subs_resolution           true
% 3.34/1.02  --res_backward_subs_resolution          true
% 3.34/1.02  --res_orphan_elimination                true
% 3.34/1.02  --res_time_limit                        2.
% 3.34/1.02  --res_out_proof                         true
% 3.34/1.02  
% 3.34/1.02  ------ Superposition Options
% 3.34/1.02  
% 3.34/1.02  --superposition_flag                    true
% 3.34/1.02  --sup_passive_queue_type                priority_queues
% 3.34/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.34/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.34/1.02  --demod_completeness_check              fast
% 3.34/1.02  --demod_use_ground                      true
% 3.34/1.02  --sup_to_prop_solver                    passive
% 3.34/1.02  --sup_prop_simpl_new                    true
% 3.34/1.02  --sup_prop_simpl_given                  true
% 3.34/1.02  --sup_fun_splitting                     false
% 3.34/1.02  --sup_smt_interval                      50000
% 3.34/1.02  
% 3.34/1.02  ------ Superposition Simplification Setup
% 3.34/1.02  
% 3.34/1.02  --sup_indices_passive                   []
% 3.34/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.34/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/1.02  --sup_full_bw                           [BwDemod]
% 3.34/1.02  --sup_immed_triv                        [TrivRules]
% 3.34/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.34/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/1.02  --sup_immed_bw_main                     []
% 3.34/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.34/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.34/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.34/1.02  
% 3.34/1.02  ------ Combination Options
% 3.34/1.02  
% 3.34/1.02  --comb_res_mult                         3
% 3.34/1.02  --comb_sup_mult                         2
% 3.34/1.02  --comb_inst_mult                        10
% 3.34/1.02  
% 3.34/1.02  ------ Debug Options
% 3.34/1.02  
% 3.34/1.02  --dbg_backtrace                         false
% 3.34/1.02  --dbg_dump_prop_clauses                 false
% 3.34/1.02  --dbg_dump_prop_clauses_file            -
% 3.34/1.02  --dbg_out_stat                          false
% 3.34/1.02  ------ Parsing...
% 3.34/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.34/1.02  
% 3.34/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.34/1.02  
% 3.34/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.34/1.02  
% 3.34/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.34/1.02  ------ Proving...
% 3.34/1.02  ------ Problem Properties 
% 3.34/1.02  
% 3.34/1.02  
% 3.34/1.02  clauses                                 31
% 3.34/1.02  conjectures                             3
% 3.34/1.02  EPR                                     3
% 3.34/1.02  Horn                                    26
% 3.34/1.02  unary                                   12
% 3.34/1.02  binary                                  11
% 3.34/1.02  lits                                    61
% 3.34/1.02  lits eq                                 23
% 3.34/1.02  fd_pure                                 0
% 3.34/1.02  fd_pseudo                               0
% 3.34/1.02  fd_cond                                 2
% 3.34/1.02  fd_pseudo_cond                          4
% 3.34/1.02  AC symbols                              0
% 3.34/1.02  
% 3.34/1.02  ------ Schedule dynamic 5 is on 
% 3.34/1.02  
% 3.34/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.34/1.02  
% 3.34/1.02  
% 3.34/1.02  ------ 
% 3.34/1.02  Current options:
% 3.34/1.02  ------ 
% 3.34/1.02  
% 3.34/1.02  ------ Input Options
% 3.34/1.02  
% 3.34/1.02  --out_options                           all
% 3.34/1.02  --tptp_safe_out                         true
% 3.34/1.02  --problem_path                          ""
% 3.34/1.02  --include_path                          ""
% 3.34/1.02  --clausifier                            res/vclausify_rel
% 3.34/1.02  --clausifier_options                    --mode clausify
% 3.34/1.02  --stdin                                 false
% 3.34/1.02  --stats_out                             all
% 3.34/1.02  
% 3.34/1.02  ------ General Options
% 3.34/1.02  
% 3.34/1.02  --fof                                   false
% 3.34/1.02  --time_out_real                         305.
% 3.34/1.02  --time_out_virtual                      -1.
% 3.34/1.02  --symbol_type_check                     false
% 3.34/1.02  --clausify_out                          false
% 3.34/1.02  --sig_cnt_out                           false
% 3.34/1.02  --trig_cnt_out                          false
% 3.34/1.02  --trig_cnt_out_tolerance                1.
% 3.34/1.02  --trig_cnt_out_sk_spl                   false
% 3.34/1.02  --abstr_cl_out                          false
% 3.34/1.02  
% 3.34/1.02  ------ Global Options
% 3.34/1.02  
% 3.34/1.02  --schedule                              default
% 3.34/1.02  --add_important_lit                     false
% 3.34/1.02  --prop_solver_per_cl                    1000
% 3.34/1.02  --min_unsat_core                        false
% 3.34/1.02  --soft_assumptions                      false
% 3.34/1.02  --soft_lemma_size                       3
% 3.34/1.02  --prop_impl_unit_size                   0
% 3.34/1.02  --prop_impl_unit                        []
% 3.34/1.02  --share_sel_clauses                     true
% 3.34/1.02  --reset_solvers                         false
% 3.34/1.02  --bc_imp_inh                            [conj_cone]
% 3.34/1.02  --conj_cone_tolerance                   3.
% 3.34/1.02  --extra_neg_conj                        none
% 3.34/1.02  --large_theory_mode                     true
% 3.34/1.02  --prolific_symb_bound                   200
% 3.34/1.02  --lt_threshold                          2000
% 3.34/1.02  --clause_weak_htbl                      true
% 3.34/1.02  --gc_record_bc_elim                     false
% 3.34/1.02  
% 3.34/1.02  ------ Preprocessing Options
% 3.34/1.02  
% 3.34/1.02  --preprocessing_flag                    true
% 3.34/1.02  --time_out_prep_mult                    0.1
% 3.34/1.02  --splitting_mode                        input
% 3.34/1.02  --splitting_grd                         true
% 3.34/1.02  --splitting_cvd                         false
% 3.34/1.02  --splitting_cvd_svl                     false
% 3.34/1.02  --splitting_nvd                         32
% 3.34/1.02  --sub_typing                            true
% 3.34/1.02  --prep_gs_sim                           true
% 3.34/1.02  --prep_unflatten                        true
% 3.34/1.02  --prep_res_sim                          true
% 3.34/1.02  --prep_upred                            true
% 3.34/1.02  --prep_sem_filter                       exhaustive
% 3.34/1.02  --prep_sem_filter_out                   false
% 3.34/1.02  --pred_elim                             true
% 3.34/1.02  --res_sim_input                         true
% 3.34/1.02  --eq_ax_congr_red                       true
% 3.34/1.02  --pure_diseq_elim                       true
% 3.34/1.02  --brand_transform                       false
% 3.34/1.02  --non_eq_to_eq                          false
% 3.34/1.02  --prep_def_merge                        true
% 3.34/1.02  --prep_def_merge_prop_impl              false
% 3.34/1.02  --prep_def_merge_mbd                    true
% 3.34/1.02  --prep_def_merge_tr_red                 false
% 3.34/1.02  --prep_def_merge_tr_cl                  false
% 3.34/1.02  --smt_preprocessing                     true
% 3.34/1.02  --smt_ac_axioms                         fast
% 3.34/1.02  --preprocessed_out                      false
% 3.34/1.02  --preprocessed_stats                    false
% 3.34/1.02  
% 3.34/1.02  ------ Abstraction refinement Options
% 3.34/1.02  
% 3.34/1.02  --abstr_ref                             []
% 3.34/1.02  --abstr_ref_prep                        false
% 3.34/1.02  --abstr_ref_until_sat                   false
% 3.34/1.02  --abstr_ref_sig_restrict                funpre
% 3.34/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.34/1.02  --abstr_ref_under                       []
% 3.34/1.02  
% 3.34/1.02  ------ SAT Options
% 3.34/1.02  
% 3.34/1.02  --sat_mode                              false
% 3.34/1.02  --sat_fm_restart_options                ""
% 3.34/1.02  --sat_gr_def                            false
% 3.34/1.02  --sat_epr_types                         true
% 3.34/1.02  --sat_non_cyclic_types                  false
% 3.34/1.02  --sat_finite_models                     false
% 3.34/1.02  --sat_fm_lemmas                         false
% 3.34/1.02  --sat_fm_prep                           false
% 3.34/1.02  --sat_fm_uc_incr                        true
% 3.34/1.02  --sat_out_model                         small
% 3.34/1.02  --sat_out_clauses                       false
% 3.34/1.02  
% 3.34/1.02  ------ QBF Options
% 3.34/1.02  
% 3.34/1.02  --qbf_mode                              false
% 3.34/1.02  --qbf_elim_univ                         false
% 3.34/1.02  --qbf_dom_inst                          none
% 3.34/1.02  --qbf_dom_pre_inst                      false
% 3.34/1.02  --qbf_sk_in                             false
% 3.34/1.02  --qbf_pred_elim                         true
% 3.34/1.02  --qbf_split                             512
% 3.34/1.02  
% 3.34/1.02  ------ BMC1 Options
% 3.34/1.02  
% 3.34/1.02  --bmc1_incremental                      false
% 3.34/1.02  --bmc1_axioms                           reachable_all
% 3.34/1.02  --bmc1_min_bound                        0
% 3.34/1.02  --bmc1_max_bound                        -1
% 3.34/1.02  --bmc1_max_bound_default                -1
% 3.34/1.02  --bmc1_symbol_reachability              true
% 3.34/1.02  --bmc1_property_lemmas                  false
% 3.34/1.02  --bmc1_k_induction                      false
% 3.34/1.02  --bmc1_non_equiv_states                 false
% 3.34/1.02  --bmc1_deadlock                         false
% 3.34/1.02  --bmc1_ucm                              false
% 3.34/1.02  --bmc1_add_unsat_core                   none
% 3.34/1.02  --bmc1_unsat_core_children              false
% 3.34/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.34/1.02  --bmc1_out_stat                         full
% 3.34/1.02  --bmc1_ground_init                      false
% 3.34/1.02  --bmc1_pre_inst_next_state              false
% 3.34/1.02  --bmc1_pre_inst_state                   false
% 3.34/1.02  --bmc1_pre_inst_reach_state             false
% 3.34/1.02  --bmc1_out_unsat_core                   false
% 3.34/1.02  --bmc1_aig_witness_out                  false
% 3.34/1.02  --bmc1_verbose                          false
% 3.34/1.02  --bmc1_dump_clauses_tptp                false
% 3.34/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.34/1.02  --bmc1_dump_file                        -
% 3.34/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.34/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.34/1.02  --bmc1_ucm_extend_mode                  1
% 3.34/1.02  --bmc1_ucm_init_mode                    2
% 3.34/1.02  --bmc1_ucm_cone_mode                    none
% 3.34/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.34/1.02  --bmc1_ucm_relax_model                  4
% 3.34/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.34/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.34/1.02  --bmc1_ucm_layered_model                none
% 3.34/1.02  --bmc1_ucm_max_lemma_size               10
% 3.34/1.02  
% 3.34/1.02  ------ AIG Options
% 3.34/1.02  
% 3.34/1.02  --aig_mode                              false
% 3.34/1.02  
% 3.34/1.02  ------ Instantiation Options
% 3.34/1.02  
% 3.34/1.02  --instantiation_flag                    true
% 3.34/1.02  --inst_sos_flag                         false
% 3.34/1.02  --inst_sos_phase                        true
% 3.34/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.34/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.34/1.02  --inst_lit_sel_side                     none
% 3.34/1.02  --inst_solver_per_active                1400
% 3.34/1.02  --inst_solver_calls_frac                1.
% 3.34/1.02  --inst_passive_queue_type               priority_queues
% 3.34/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.34/1.02  --inst_passive_queues_freq              [25;2]
% 3.34/1.02  --inst_dismatching                      true
% 3.34/1.02  --inst_eager_unprocessed_to_passive     true
% 3.34/1.02  --inst_prop_sim_given                   true
% 3.34/1.02  --inst_prop_sim_new                     false
% 3.34/1.02  --inst_subs_new                         false
% 3.34/1.02  --inst_eq_res_simp                      false
% 3.34/1.02  --inst_subs_given                       false
% 3.34/1.02  --inst_orphan_elimination               true
% 3.34/1.02  --inst_learning_loop_flag               true
% 3.34/1.02  --inst_learning_start                   3000
% 3.34/1.02  --inst_learning_factor                  2
% 3.34/1.02  --inst_start_prop_sim_after_learn       3
% 3.34/1.02  --inst_sel_renew                        solver
% 3.34/1.02  --inst_lit_activity_flag                true
% 3.34/1.02  --inst_restr_to_given                   false
% 3.34/1.02  --inst_activity_threshold               500
% 3.34/1.02  --inst_out_proof                        true
% 3.34/1.02  
% 3.34/1.02  ------ Resolution Options
% 3.34/1.02  
% 3.34/1.02  --resolution_flag                       false
% 3.34/1.02  --res_lit_sel                           adaptive
% 3.34/1.02  --res_lit_sel_side                      none
% 3.34/1.02  --res_ordering                          kbo
% 3.34/1.02  --res_to_prop_solver                    active
% 3.34/1.02  --res_prop_simpl_new                    false
% 3.34/1.02  --res_prop_simpl_given                  true
% 3.34/1.02  --res_passive_queue_type                priority_queues
% 3.34/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.34/1.02  --res_passive_queues_freq               [15;5]
% 3.34/1.02  --res_forward_subs                      full
% 3.34/1.02  --res_backward_subs                     full
% 3.34/1.02  --res_forward_subs_resolution           true
% 3.34/1.02  --res_backward_subs_resolution          true
% 3.34/1.02  --res_orphan_elimination                true
% 3.34/1.02  --res_time_limit                        2.
% 3.34/1.02  --res_out_proof                         true
% 3.34/1.02  
% 3.34/1.02  ------ Superposition Options
% 3.34/1.02  
% 3.34/1.02  --superposition_flag                    true
% 3.34/1.02  --sup_passive_queue_type                priority_queues
% 3.34/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.34/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.34/1.02  --demod_completeness_check              fast
% 3.34/1.02  --demod_use_ground                      true
% 3.34/1.02  --sup_to_prop_solver                    passive
% 3.34/1.02  --sup_prop_simpl_new                    true
% 3.34/1.02  --sup_prop_simpl_given                  true
% 3.34/1.02  --sup_fun_splitting                     false
% 3.34/1.02  --sup_smt_interval                      50000
% 3.34/1.02  
% 3.34/1.02  ------ Superposition Simplification Setup
% 3.34/1.02  
% 3.34/1.02  --sup_indices_passive                   []
% 3.34/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.34/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/1.02  --sup_full_bw                           [BwDemod]
% 3.34/1.02  --sup_immed_triv                        [TrivRules]
% 3.34/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.34/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/1.02  --sup_immed_bw_main                     []
% 3.34/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.34/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.34/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.34/1.02  
% 3.34/1.02  ------ Combination Options
% 3.34/1.02  
% 3.34/1.02  --comb_res_mult                         3
% 3.34/1.02  --comb_sup_mult                         2
% 3.34/1.02  --comb_inst_mult                        10
% 3.34/1.02  
% 3.34/1.02  ------ Debug Options
% 3.34/1.02  
% 3.34/1.02  --dbg_backtrace                         false
% 3.34/1.02  --dbg_dump_prop_clauses                 false
% 3.34/1.02  --dbg_dump_prop_clauses_file            -
% 3.34/1.02  --dbg_out_stat                          false
% 3.34/1.02  
% 3.34/1.02  
% 3.34/1.02  
% 3.34/1.02  
% 3.34/1.02  ------ Proving...
% 3.34/1.02  
% 3.34/1.02  
% 3.34/1.02  % SZS status Theorem for theBenchmark.p
% 3.34/1.02  
% 3.34/1.02   Resolution empty clause
% 3.34/1.02  
% 3.34/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.34/1.02  
% 3.34/1.02  fof(f3,axiom,(
% 3.34/1.02    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.34/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.02  
% 3.34/1.02  fof(f44,plain,(
% 3.34/1.02    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.34/1.02    inference(nnf_transformation,[],[f3])).
% 3.34/1.02  
% 3.34/1.02  fof(f45,plain,(
% 3.34/1.02    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.34/1.02    inference(flattening,[],[f44])).
% 3.34/1.02  
% 3.34/1.02  fof(f56,plain,(
% 3.34/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.34/1.02    inference(cnf_transformation,[],[f45])).
% 3.34/1.02  
% 3.34/1.02  fof(f116,plain,(
% 3.34/1.02    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.34/1.02    inference(equality_resolution,[],[f56])).
% 3.34/1.02  
% 3.34/1.02  fof(f15,axiom,(
% 3.34/1.02    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 3.34/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.02  
% 3.34/1.02  fof(f46,plain,(
% 3.34/1.02    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.34/1.02    inference(nnf_transformation,[],[f15])).
% 3.34/1.02  
% 3.34/1.02  fof(f47,plain,(
% 3.34/1.02    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.34/1.02    inference(rectify,[],[f46])).
% 3.34/1.02  
% 3.34/1.02  fof(f48,plain,(
% 3.34/1.02    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 3.34/1.02    introduced(choice_axiom,[])).
% 3.34/1.02  
% 3.34/1.02  fof(f49,plain,(
% 3.34/1.02    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.34/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f47,f48])).
% 3.34/1.02  
% 3.34/1.02  fof(f71,plain,(
% 3.34/1.02    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 3.34/1.02    inference(cnf_transformation,[],[f49])).
% 3.34/1.02  
% 3.34/1.02  fof(f117,plain,(
% 3.34/1.02    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 3.34/1.02    inference(equality_resolution,[],[f71])).
% 3.34/1.02  
% 3.34/1.02  fof(f2,axiom,(
% 3.34/1.02    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 3.34/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.02  
% 3.34/1.02  fof(f29,plain,(
% 3.34/1.02    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 3.34/1.02    inference(ennf_transformation,[],[f2])).
% 3.34/1.02  
% 3.34/1.02  fof(f42,plain,(
% 3.34/1.02    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.34/1.02    introduced(choice_axiom,[])).
% 3.34/1.02  
% 3.34/1.02  fof(f43,plain,(
% 3.34/1.02    ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0)),
% 3.34/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f42])).
% 3.34/1.02  
% 3.34/1.02  fof(f55,plain,(
% 3.34/1.02    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 3.34/1.02    inference(cnf_transformation,[],[f43])).
% 3.34/1.02  
% 3.34/1.02  fof(f27,conjecture,(
% 3.34/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 3.34/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.02  
% 3.34/1.02  fof(f28,negated_conjecture,(
% 3.34/1.02    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 3.34/1.02    inference(negated_conjecture,[],[f27])).
% 3.34/1.02  
% 3.34/1.02  fof(f40,plain,(
% 3.34/1.02    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 3.34/1.02    inference(ennf_transformation,[],[f28])).
% 3.34/1.02  
% 3.34/1.02  fof(f41,plain,(
% 3.34/1.02    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 3.34/1.02    inference(flattening,[],[f40])).
% 3.34/1.02  
% 3.34/1.02  fof(f52,plain,(
% 3.34/1.02    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (~r2_hidden(k1_funct_1(sK4,sK2),sK3) & k1_xboole_0 != sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) & v1_funct_2(sK4,k1_tarski(sK2),sK3) & v1_funct_1(sK4))),
% 3.34/1.02    introduced(choice_axiom,[])).
% 3.34/1.02  
% 3.34/1.02  fof(f53,plain,(
% 3.34/1.02    ~r2_hidden(k1_funct_1(sK4,sK2),sK3) & k1_xboole_0 != sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) & v1_funct_2(sK4,k1_tarski(sK2),sK3) & v1_funct_1(sK4)),
% 3.34/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f41,f52])).
% 3.34/1.02  
% 3.34/1.02  fof(f96,plain,(
% 3.34/1.02    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))),
% 3.34/1.02    inference(cnf_transformation,[],[f53])).
% 3.34/1.02  
% 3.34/1.02  fof(f8,axiom,(
% 3.34/1.02    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.34/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.02  
% 3.34/1.02  fof(f63,plain,(
% 3.34/1.02    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.34/1.02    inference(cnf_transformation,[],[f8])).
% 3.34/1.02  
% 3.34/1.02  fof(f9,axiom,(
% 3.34/1.02    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.34/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.02  
% 3.34/1.02  fof(f64,plain,(
% 3.34/1.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.34/1.02    inference(cnf_transformation,[],[f9])).
% 3.34/1.02  
% 3.34/1.02  fof(f10,axiom,(
% 3.34/1.02    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.34/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.02  
% 3.34/1.02  fof(f65,plain,(
% 3.34/1.02    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.34/1.02    inference(cnf_transformation,[],[f10])).
% 3.34/1.02  
% 3.34/1.02  fof(f11,axiom,(
% 3.34/1.02    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.34/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.02  
% 3.34/1.02  fof(f66,plain,(
% 3.34/1.02    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.34/1.02    inference(cnf_transformation,[],[f11])).
% 3.34/1.02  
% 3.34/1.02  fof(f12,axiom,(
% 3.34/1.02    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.34/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.02  
% 3.34/1.02  fof(f67,plain,(
% 3.34/1.02    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.34/1.02    inference(cnf_transformation,[],[f12])).
% 3.34/1.02  
% 3.34/1.02  fof(f13,axiom,(
% 3.34/1.02    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.34/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.02  
% 3.34/1.02  fof(f68,plain,(
% 3.34/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.34/1.02    inference(cnf_transformation,[],[f13])).
% 3.34/1.02  
% 3.34/1.02  fof(f14,axiom,(
% 3.34/1.02    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.34/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.02  
% 3.34/1.02  fof(f69,plain,(
% 3.34/1.02    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.34/1.02    inference(cnf_transformation,[],[f14])).
% 3.34/1.02  
% 3.34/1.02  fof(f99,plain,(
% 3.34/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.34/1.02    inference(definition_unfolding,[],[f68,f69])).
% 3.34/1.02  
% 3.34/1.02  fof(f100,plain,(
% 3.34/1.02    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.34/1.02    inference(definition_unfolding,[],[f67,f99])).
% 3.34/1.02  
% 3.34/1.02  fof(f101,plain,(
% 3.34/1.02    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.34/1.02    inference(definition_unfolding,[],[f66,f100])).
% 3.34/1.02  
% 3.34/1.02  fof(f102,plain,(
% 3.34/1.02    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.34/1.02    inference(definition_unfolding,[],[f65,f101])).
% 3.34/1.02  
% 3.34/1.02  fof(f103,plain,(
% 3.34/1.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.34/1.02    inference(definition_unfolding,[],[f64,f102])).
% 3.34/1.02  
% 3.34/1.02  fof(f106,plain,(
% 3.34/1.02    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.34/1.02    inference(definition_unfolding,[],[f63,f103])).
% 3.34/1.02  
% 3.34/1.02  fof(f113,plain,(
% 3.34/1.02    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))),
% 3.34/1.02    inference(definition_unfolding,[],[f96,f106])).
% 3.34/1.02  
% 3.34/1.02  fof(f22,axiom,(
% 3.34/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.34/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.02  
% 3.34/1.02  fof(f33,plain,(
% 3.34/1.02    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.34/1.02    inference(ennf_transformation,[],[f22])).
% 3.34/1.02  
% 3.34/1.02  fof(f82,plain,(
% 3.34/1.02    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.34/1.02    inference(cnf_transformation,[],[f33])).
% 3.34/1.02  
% 3.34/1.02  fof(f25,axiom,(
% 3.34/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.34/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.02  
% 3.34/1.02  fof(f36,plain,(
% 3.34/1.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.34/1.02    inference(ennf_transformation,[],[f25])).
% 3.34/1.02  
% 3.34/1.02  fof(f37,plain,(
% 3.34/1.02    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.34/1.02    inference(flattening,[],[f36])).
% 3.34/1.02  
% 3.34/1.02  fof(f51,plain,(
% 3.34/1.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.34/1.02    inference(nnf_transformation,[],[f37])).
% 3.34/1.02  
% 3.34/1.02  fof(f87,plain,(
% 3.34/1.02    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.34/1.02    inference(cnf_transformation,[],[f51])).
% 3.34/1.02  
% 3.34/1.02  fof(f95,plain,(
% 3.34/1.02    v1_funct_2(sK4,k1_tarski(sK2),sK3)),
% 3.34/1.02    inference(cnf_transformation,[],[f53])).
% 3.34/1.02  
% 3.34/1.02  fof(f114,plain,(
% 3.34/1.02    v1_funct_2(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)),
% 3.34/1.02    inference(definition_unfolding,[],[f95,f106])).
% 3.34/1.02  
% 3.34/1.02  fof(f97,plain,(
% 3.34/1.02    k1_xboole_0 != sK3),
% 3.34/1.02    inference(cnf_transformation,[],[f53])).
% 3.34/1.02  
% 3.34/1.02  fof(f17,axiom,(
% 3.34/1.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.34/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.02  
% 3.34/1.02  fof(f30,plain,(
% 3.34/1.02    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.34/1.02    inference(ennf_transformation,[],[f17])).
% 3.34/1.02  
% 3.34/1.02  fof(f76,plain,(
% 3.34/1.02    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.34/1.02    inference(cnf_transformation,[],[f30])).
% 3.34/1.02  
% 3.34/1.02  fof(f24,axiom,(
% 3.34/1.02    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) => (r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1))),
% 3.34/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.02  
% 3.34/1.02  fof(f35,plain,(
% 3.34/1.02    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1) | ~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)))),
% 3.34/1.02    inference(ennf_transformation,[],[f24])).
% 3.34/1.02  
% 3.34/1.02  fof(f85,plain,(
% 3.34/1.02    ( ! [X2,X0,X1] : (k1_mcart_1(X0) = X1 | ~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))) )),
% 3.34/1.02    inference(cnf_transformation,[],[f35])).
% 3.34/1.02  
% 3.34/1.02  fof(f112,plain,(
% 3.34/1.02    ( ! [X2,X0,X1] : (k1_mcart_1(X0) = X1 | ~r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2))) )),
% 3.34/1.02    inference(definition_unfolding,[],[f85,f106])).
% 3.34/1.02  
% 3.34/1.02  fof(f23,axiom,(
% 3.34/1.02    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 3.34/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.02  
% 3.34/1.02  fof(f34,plain,(
% 3.34/1.02    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 3.34/1.02    inference(ennf_transformation,[],[f23])).
% 3.34/1.02  
% 3.34/1.02  fof(f83,plain,(
% 3.34/1.02    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 3.34/1.02    inference(cnf_transformation,[],[f34])).
% 3.34/1.02  
% 3.34/1.02  fof(f26,axiom,(
% 3.34/1.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 3.34/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.02  
% 3.34/1.02  fof(f38,plain,(
% 3.34/1.02    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.34/1.02    inference(ennf_transformation,[],[f26])).
% 3.34/1.02  
% 3.34/1.02  fof(f39,plain,(
% 3.34/1.02    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.34/1.02    inference(flattening,[],[f38])).
% 3.34/1.02  
% 3.34/1.02  fof(f93,plain,(
% 3.34/1.02    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.34/1.02    inference(cnf_transformation,[],[f39])).
% 3.34/1.02  
% 3.34/1.02  fof(f94,plain,(
% 3.34/1.02    v1_funct_1(sK4)),
% 3.34/1.02    inference(cnf_transformation,[],[f53])).
% 3.34/1.02  
% 3.34/1.02  fof(f98,plain,(
% 3.34/1.02    ~r2_hidden(k1_funct_1(sK4,sK2),sK3)),
% 3.34/1.02    inference(cnf_transformation,[],[f53])).
% 3.34/1.02  
% 3.34/1.02  fof(f7,axiom,(
% 3.34/1.02    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.34/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.02  
% 3.34/1.02  fof(f62,plain,(
% 3.34/1.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.34/1.02    inference(cnf_transformation,[],[f7])).
% 3.34/1.02  
% 3.34/1.02  fof(f108,plain,(
% 3.34/1.02    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) )),
% 3.34/1.02    inference(definition_unfolding,[],[f62,f103,f103])).
% 3.34/1.02  
% 3.34/1.02  fof(f16,axiom,(
% 3.34/1.02    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) <=> ~r2_hidden(X0,X1))),
% 3.34/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.02  
% 3.34/1.02  fof(f50,plain,(
% 3.34/1.02    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) | r2_hidden(X0,X1)) & (~r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)))),
% 3.34/1.02    inference(nnf_transformation,[],[f16])).
% 3.34/1.02  
% 3.34/1.02  fof(f74,plain,(
% 3.34/1.02    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)) )),
% 3.34/1.02    inference(cnf_transformation,[],[f50])).
% 3.34/1.02  
% 3.34/1.02  fof(f4,axiom,(
% 3.34/1.02    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 3.34/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.02  
% 3.34/1.02  fof(f59,plain,(
% 3.34/1.02    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 3.34/1.02    inference(cnf_transformation,[],[f4])).
% 3.34/1.02  
% 3.34/1.02  fof(f19,axiom,(
% 3.34/1.02    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.34/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.02  
% 3.34/1.02  fof(f78,plain,(
% 3.34/1.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.34/1.02    inference(cnf_transformation,[],[f19])).
% 3.34/1.02  
% 3.34/1.02  fof(f104,plain,(
% 3.34/1.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.34/1.02    inference(definition_unfolding,[],[f78,f103])).
% 3.34/1.02  
% 3.34/1.02  fof(f105,plain,(
% 3.34/1.02    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k4_xboole_0(X0,X1)) )),
% 3.34/1.02    inference(definition_unfolding,[],[f59,f104])).
% 3.34/1.02  
% 3.34/1.02  fof(f110,plain,(
% 3.34/1.02    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.34/1.02    inference(definition_unfolding,[],[f74,f105,f106,f106])).
% 3.34/1.02  
% 3.34/1.02  fof(f5,axiom,(
% 3.34/1.02    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 3.34/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.02  
% 3.34/1.02  fof(f60,plain,(
% 3.34/1.02    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 3.34/1.02    inference(cnf_transformation,[],[f5])).
% 3.34/1.02  
% 3.34/1.02  fof(f107,plain,(
% 3.34/1.02    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) )),
% 3.34/1.02    inference(definition_unfolding,[],[f60,f104])).
% 3.34/1.02  
% 3.34/1.02  fof(f21,axiom,(
% 3.34/1.02    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.34/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.02  
% 3.34/1.02  fof(f80,plain,(
% 3.34/1.02    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.34/1.02    inference(cnf_transformation,[],[f21])).
% 3.34/1.02  
% 3.34/1.02  fof(f6,axiom,(
% 3.34/1.02    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.34/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.02  
% 3.34/1.02  fof(f61,plain,(
% 3.34/1.02    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.34/1.02    inference(cnf_transformation,[],[f6])).
% 3.34/1.02  
% 3.34/1.02  fof(f1,axiom,(
% 3.34/1.02    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 3.34/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.02  
% 3.34/1.02  fof(f54,plain,(
% 3.34/1.02    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 3.34/1.02    inference(cnf_transformation,[],[f1])).
% 3.34/1.02  
% 3.34/1.02  cnf(c_4,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f116]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_1421,plain,
% 3.34/1.02      ( r1_tarski(X0,X0) = iProver_top ),
% 3.34/1.02      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_10,plain,
% 3.34/1.02      ( ~ r1_tarski(X0,X1) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 3.34/1.02      inference(cnf_transformation,[],[f117]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_1418,plain,
% 3.34/1.02      ( r1_tarski(X0,X1) != iProver_top
% 3.34/1.02      | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
% 3.34/1.02      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_1,plain,
% 3.34/1.02      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 3.34/1.02      inference(cnf_transformation,[],[f55]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_1423,plain,
% 3.34/1.02      ( k1_xboole_0 = X0 | r2_hidden(sK0(X0),X0) = iProver_top ),
% 3.34/1.02      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_33,negated_conjecture,
% 3.34/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) ),
% 3.34/1.02      inference(cnf_transformation,[],[f113]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_1405,plain,
% 3.34/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) = iProver_top ),
% 3.34/1.02      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_19,plain,
% 3.34/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/1.02      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.34/1.02      inference(cnf_transformation,[],[f82]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_1411,plain,
% 3.34/1.02      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.34/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.34/1.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_2742,plain,
% 3.34/1.02      ( k1_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4) = k1_relat_1(sK4) ),
% 3.34/1.02      inference(superposition,[status(thm)],[c_1405,c_1411]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_29,plain,
% 3.34/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.34/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/1.02      | k1_relset_1(X1,X2,X0) = X1
% 3.34/1.02      | k1_xboole_0 = X2 ),
% 3.34/1.02      inference(cnf_transformation,[],[f87]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_34,negated_conjecture,
% 3.34/1.02      ( v1_funct_2(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) ),
% 3.34/1.02      inference(cnf_transformation,[],[f114]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_509,plain,
% 3.34/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/1.02      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != X1
% 3.34/1.02      | k1_relset_1(X1,X2,X0) = X1
% 3.34/1.02      | sK3 != X2
% 3.34/1.02      | sK4 != X0
% 3.34/1.02      | k1_xboole_0 = X2 ),
% 3.34/1.02      inference(resolution_lifted,[status(thm)],[c_29,c_34]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_510,plain,
% 3.34/1.02      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))
% 3.34/1.02      | k1_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 3.34/1.02      | k1_xboole_0 = sK3 ),
% 3.34/1.02      inference(unflattening,[status(thm)],[c_509]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_32,negated_conjecture,
% 3.34/1.02      ( k1_xboole_0 != sK3 ),
% 3.34/1.02      inference(cnf_transformation,[],[f97]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_512,plain,
% 3.34/1.02      ( k1_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 3.34/1.02      inference(global_propositional_subsumption,
% 3.34/1.02                [status(thm)],
% 3.34/1.02                [c_510,c_33,c_32]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_2750,plain,
% 3.34/1.02      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_relat_1(sK4) ),
% 3.34/1.02      inference(demodulation,[status(thm)],[c_2742,c_512]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_2939,plain,
% 3.34/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3))) = iProver_top ),
% 3.34/1.02      inference(demodulation,[status(thm)],[c_2750,c_1405]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_14,plain,
% 3.34/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.34/1.02      | ~ r2_hidden(X2,X0)
% 3.34/1.02      | r2_hidden(X2,X1) ),
% 3.34/1.02      inference(cnf_transformation,[],[f76]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_1414,plain,
% 3.34/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.34/1.02      | r2_hidden(X2,X0) != iProver_top
% 3.34/1.02      | r2_hidden(X2,X1) = iProver_top ),
% 3.34/1.02      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_3679,plain,
% 3.34/1.02      ( r2_hidden(X0,k2_zfmisc_1(k1_relat_1(sK4),sK3)) = iProver_top
% 3.34/1.02      | r2_hidden(X0,sK4) != iProver_top ),
% 3.34/1.02      inference(superposition,[status(thm)],[c_2939,c_1414]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_23,plain,
% 3.34/1.02      ( ~ r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2))
% 3.34/1.02      | k1_mcart_1(X0) = X1 ),
% 3.34/1.02      inference(cnf_transformation,[],[f112]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_1407,plain,
% 3.34/1.02      ( k1_mcart_1(X0) = X1
% 3.34/1.02      | r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)) != iProver_top ),
% 3.34/1.02      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_2959,plain,
% 3.34/1.02      ( k1_mcart_1(X0) = sK2
% 3.34/1.02      | r2_hidden(X0,k2_zfmisc_1(k1_relat_1(sK4),X1)) != iProver_top ),
% 3.34/1.02      inference(superposition,[status(thm)],[c_2750,c_1407]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_4094,plain,
% 3.34/1.02      ( k1_mcart_1(X0) = sK2 | r2_hidden(X0,sK4) != iProver_top ),
% 3.34/1.02      inference(superposition,[status(thm)],[c_3679,c_2959]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_4202,plain,
% 3.34/1.02      ( k1_mcart_1(sK0(sK4)) = sK2 | sK4 = k1_xboole_0 ),
% 3.34/1.02      inference(superposition,[status(thm)],[c_1423,c_4094]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_21,plain,
% 3.34/1.02      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1) ),
% 3.34/1.02      inference(cnf_transformation,[],[f83]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_1409,plain,
% 3.34/1.02      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.34/1.02      | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
% 3.34/1.02      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_4093,plain,
% 3.34/1.02      ( r2_hidden(X0,sK4) != iProver_top
% 3.34/1.02      | r2_hidden(k1_mcart_1(X0),k1_relat_1(sK4)) = iProver_top ),
% 3.34/1.02      inference(superposition,[status(thm)],[c_3679,c_1409]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_5653,plain,
% 3.34/1.02      ( sK4 = k1_xboole_0
% 3.34/1.02      | r2_hidden(sK0(sK4),sK4) != iProver_top
% 3.34/1.02      | r2_hidden(sK2,k1_relat_1(sK4)) = iProver_top ),
% 3.34/1.02      inference(superposition,[status(thm)],[c_4202,c_4093]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_30,plain,
% 3.34/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.34/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/1.02      | ~ r2_hidden(X3,X1)
% 3.34/1.02      | r2_hidden(k1_funct_1(X0,X3),X2)
% 3.34/1.02      | ~ v1_funct_1(X0)
% 3.34/1.02      | k1_xboole_0 = X2 ),
% 3.34/1.02      inference(cnf_transformation,[],[f93]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_35,negated_conjecture,
% 3.34/1.02      ( v1_funct_1(sK4) ),
% 3.34/1.02      inference(cnf_transformation,[],[f94]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_414,plain,
% 3.34/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.34/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/1.02      | ~ r2_hidden(X3,X1)
% 3.34/1.02      | r2_hidden(k1_funct_1(X0,X3),X2)
% 3.34/1.02      | sK4 != X0
% 3.34/1.02      | k1_xboole_0 = X2 ),
% 3.34/1.02      inference(resolution_lifted,[status(thm)],[c_30,c_35]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_415,plain,
% 3.34/1.02      ( ~ v1_funct_2(sK4,X0,X1)
% 3.34/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.34/1.02      | ~ r2_hidden(X2,X0)
% 3.34/1.02      | r2_hidden(k1_funct_1(sK4,X2),X1)
% 3.34/1.02      | k1_xboole_0 = X1 ),
% 3.34/1.02      inference(unflattening,[status(thm)],[c_414]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_536,plain,
% 3.34/1.02      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.34/1.02      | ~ r2_hidden(X2,X0)
% 3.34/1.02      | r2_hidden(k1_funct_1(sK4,X2),X1)
% 3.34/1.02      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != X0
% 3.34/1.02      | sK3 != X1
% 3.34/1.02      | sK4 != sK4
% 3.34/1.02      | k1_xboole_0 = X1 ),
% 3.34/1.02      inference(resolution_lifted,[status(thm)],[c_34,c_415]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_537,plain,
% 3.34/1.02      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))
% 3.34/1.02      | ~ r2_hidden(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 3.34/1.02      | r2_hidden(k1_funct_1(sK4,X0),sK3)
% 3.34/1.02      | k1_xboole_0 = sK3 ),
% 3.34/1.02      inference(unflattening,[status(thm)],[c_536]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_541,plain,
% 3.34/1.02      ( r2_hidden(k1_funct_1(sK4,X0),sK3)
% 3.34/1.02      | ~ r2_hidden(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
% 3.34/1.02      inference(global_propositional_subsumption,
% 3.34/1.02                [status(thm)],
% 3.34/1.02                [c_537,c_33,c_32]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_542,plain,
% 3.34/1.02      ( ~ r2_hidden(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 3.34/1.02      | r2_hidden(k1_funct_1(sK4,X0),sK3) ),
% 3.34/1.02      inference(renaming,[status(thm)],[c_541]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_1401,plain,
% 3.34/1.02      ( r2_hidden(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top
% 3.34/1.02      | r2_hidden(k1_funct_1(sK4,X0),sK3) = iProver_top ),
% 3.34/1.02      inference(predicate_to_equality,[status(thm)],[c_542]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_2938,plain,
% 3.34/1.02      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 3.34/1.02      | r2_hidden(k1_funct_1(sK4,X0),sK3) = iProver_top ),
% 3.34/1.02      inference(demodulation,[status(thm)],[c_2750,c_1401]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_31,negated_conjecture,
% 3.34/1.02      ( ~ r2_hidden(k1_funct_1(sK4,sK2),sK3) ),
% 3.34/1.02      inference(cnf_transformation,[],[f98]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_1406,plain,
% 3.34/1.02      ( r2_hidden(k1_funct_1(sK4,sK2),sK3) != iProver_top ),
% 3.34/1.02      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_3181,plain,
% 3.34/1.02      ( r2_hidden(sK2,k1_relat_1(sK4)) != iProver_top ),
% 3.34/1.02      inference(superposition,[status(thm)],[c_2938,c_1406]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_6035,plain,
% 3.34/1.02      ( r2_hidden(sK0(sK4),sK4) != iProver_top | sK4 = k1_xboole_0 ),
% 3.34/1.02      inference(global_propositional_subsumption,[status(thm)],[c_5653,c_3181]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_6036,plain,
% 3.34/1.02      ( sK4 = k1_xboole_0 | r2_hidden(sK0(sK4),sK4) != iProver_top ),
% 3.34/1.02      inference(renaming,[status(thm)],[c_6035]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_6041,plain,
% 3.34/1.02      ( sK4 = k1_xboole_0 ),
% 3.34/1.02      inference(superposition,[status(thm)],[c_1423,c_6036]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_7,plain,
% 3.34/1.02      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
% 3.34/1.02      inference(cnf_transformation,[],[f108]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_13,plain,
% 3.34/1.02      ( ~ r2_hidden(X0,X1)
% 3.34/1.02      | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 3.34/1.02      inference(cnf_transformation,[],[f110]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_1415,plain,
% 3.34/1.02      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
% 3.34/1.02      | r2_hidden(X0,X1) != iProver_top ),
% 3.34/1.02      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_4594,plain,
% 3.34/1.02      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
% 3.34/1.02      | r2_hidden(X0,X1) != iProver_top ),
% 3.34/1.02      inference(superposition,[status(thm)],[c_7,c_1415]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_4762,plain,
% 3.34/1.02      ( k5_xboole_0(k1_relat_1(sK4),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_relat_1(sK4)))) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 3.34/1.02      | r2_hidden(sK2,X0) != iProver_top ),
% 3.34/1.02      inference(superposition,[status(thm)],[c_2750,c_4594]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_4765,plain,
% 3.34/1.02      ( k5_xboole_0(k1_relat_1(sK4),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_relat_1(sK4)))) != k1_relat_1(sK4)
% 3.34/1.02      | r2_hidden(sK2,X0) != iProver_top ),
% 3.34/1.02      inference(light_normalisation,[status(thm)],[c_4762,c_2750]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_6967,plain,
% 3.34/1.02      ( k5_xboole_0(k1_relat_1(k1_xboole_0),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_relat_1(k1_xboole_0)))) != k1_relat_1(k1_xboole_0)
% 3.34/1.02      | r2_hidden(sK2,X0) != iProver_top ),
% 3.34/1.02      inference(demodulation,[status(thm)],[c_6041,c_4765]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_5,plain,
% 3.34/1.02      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.34/1.02      inference(cnf_transformation,[],[f107]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_18,plain,
% 3.34/1.02      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.34/1.02      inference(cnf_transformation,[],[f80]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_7042,plain,
% 3.34/1.02      ( k5_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.34/1.02      | r2_hidden(sK2,X0) != iProver_top ),
% 3.34/1.02      inference(light_normalisation,[status(thm)],[c_6967,c_5,c_18]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_6,plain,
% 3.34/1.02      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.34/1.02      inference(cnf_transformation,[],[f61]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_0,plain,
% 3.34/1.02      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 3.34/1.02      inference(cnf_transformation,[],[f54]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_1926,plain,
% 3.34/1.02      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 3.34/1.02      inference(superposition,[status(thm)],[c_6,c_0]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_7043,plain,
% 3.34/1.02      ( k1_xboole_0 != k1_xboole_0 | r2_hidden(sK2,X0) != iProver_top ),
% 3.34/1.02      inference(demodulation,[status(thm)],[c_7042,c_1926]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_7044,plain,
% 3.34/1.02      ( r2_hidden(sK2,X0) != iProver_top ),
% 3.34/1.02      inference(equality_resolution_simp,[status(thm)],[c_7043]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_9020,plain,
% 3.34/1.02      ( r1_tarski(sK2,X0) != iProver_top ),
% 3.34/1.02      inference(superposition,[status(thm)],[c_1418,c_7044]) ).
% 3.34/1.02  
% 3.34/1.02  cnf(c_9031,plain,
% 3.34/1.02      ( $false ),
% 3.34/1.02      inference(superposition,[status(thm)],[c_1421,c_9020]) ).
% 3.34/1.02  
% 3.34/1.02  
% 3.34/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.34/1.02  
% 3.34/1.02  ------                               Statistics
% 3.34/1.02  
% 3.34/1.02  ------ General
% 3.34/1.02  
% 3.34/1.02  abstr_ref_over_cycles:                  0
% 3.34/1.02  abstr_ref_under_cycles:                 0
% 3.34/1.02  gc_basic_clause_elim:                   0
% 3.34/1.02  forced_gc_time:                         0
% 3.34/1.02  parsing_time:                           0.02
% 3.34/1.02  unif_index_cands_time:                  0.
% 3.34/1.02  unif_index_add_time:                    0.
% 3.34/1.02  orderings_time:                         0.
% 3.34/1.02  out_proof_time:                         0.01
% 3.34/1.02  total_time:                             0.284
% 3.34/1.02  num_of_symbols:                         53
% 3.34/1.02  num_of_terms:                           8783
% 3.34/1.02  
% 3.34/1.02  ------ Preprocessing
% 3.34/1.02  
% 3.34/1.02  num_of_splits:                          0
% 3.34/1.02  num_of_split_atoms:                     0
% 3.34/1.02  num_of_reused_defs:                     0
% 3.34/1.02  num_eq_ax_congr_red:                    20
% 3.34/1.02  num_of_sem_filtered_clauses:            1
% 3.34/1.02  num_of_subtypes:                        0
% 3.34/1.02  monotx_restored_types:                  0
% 3.34/1.02  sat_num_of_epr_types:                   0
% 3.34/1.02  sat_num_of_non_cyclic_types:            0
% 3.34/1.02  sat_guarded_non_collapsed_types:        0
% 3.34/1.02  num_pure_diseq_elim:                    0
% 3.34/1.02  simp_replaced_by:                       0
% 3.34/1.02  res_preprocessed:                       157
% 3.34/1.02  prep_upred:                             0
% 3.34/1.02  prep_unflattend:                        38
% 3.34/1.02  smt_new_axioms:                         0
% 3.34/1.02  pred_elim_cands:                        3
% 3.34/1.02  pred_elim:                              2
% 3.34/1.02  pred_elim_cl:                           4
% 3.34/1.02  pred_elim_cycles:                       4
% 3.34/1.02  merged_defs:                            16
% 3.34/1.02  merged_defs_ncl:                        0
% 3.34/1.02  bin_hyper_res:                          16
% 3.34/1.02  prep_cycles:                            4
% 3.34/1.02  pred_elim_time:                         0.006
% 3.34/1.02  splitting_time:                         0.
% 3.34/1.02  sem_filter_time:                        0.
% 3.34/1.02  monotx_time:                            0.
% 3.34/1.02  subtype_inf_time:                       0.
% 3.34/1.02  
% 3.34/1.02  ------ Problem properties
% 3.34/1.02  
% 3.34/1.02  clauses:                                31
% 3.34/1.02  conjectures:                            3
% 3.34/1.02  epr:                                    3
% 3.34/1.02  horn:                                   26
% 3.34/1.02  ground:                                 8
% 3.34/1.02  unary:                                  12
% 3.34/1.02  binary:                                 11
% 3.34/1.02  lits:                                   61
% 3.34/1.02  lits_eq:                                23
% 3.34/1.02  fd_pure:                                0
% 3.34/1.02  fd_pseudo:                              0
% 3.34/1.02  fd_cond:                                2
% 3.34/1.02  fd_pseudo_cond:                         4
% 3.34/1.02  ac_symbols:                             0
% 3.34/1.02  
% 3.34/1.02  ------ Propositional Solver
% 3.34/1.02  
% 3.34/1.02  prop_solver_calls:                      28
% 3.34/1.02  prop_fast_solver_calls:                 932
% 3.34/1.02  smt_solver_calls:                       0
% 3.34/1.02  smt_fast_solver_calls:                  0
% 3.34/1.02  prop_num_of_clauses:                    3273
% 3.34/1.02  prop_preprocess_simplified:             9449
% 3.34/1.02  prop_fo_subsumed:                       13
% 3.34/1.02  prop_solver_time:                       0.
% 3.34/1.02  smt_solver_time:                        0.
% 3.34/1.02  smt_fast_solver_time:                   0.
% 3.34/1.02  prop_fast_solver_time:                  0.
% 3.34/1.02  prop_unsat_core_time:                   0.
% 3.34/1.02  
% 3.34/1.02  ------ QBF
% 3.34/1.02  
% 3.34/1.02  qbf_q_res:                              0
% 3.34/1.02  qbf_num_tautologies:                    0
% 3.34/1.02  qbf_prep_cycles:                        0
% 3.34/1.02  
% 3.34/1.02  ------ BMC1
% 3.34/1.02  
% 3.34/1.02  bmc1_current_bound:                     -1
% 3.34/1.02  bmc1_last_solved_bound:                 -1
% 3.34/1.02  bmc1_unsat_core_size:                   -1
% 3.34/1.02  bmc1_unsat_core_parents_size:           -1
% 3.34/1.02  bmc1_merge_next_fun:                    0
% 3.34/1.02  bmc1_unsat_core_clauses_time:           0.
% 3.34/1.02  
% 3.34/1.02  ------ Instantiation
% 3.34/1.02  
% 3.34/1.02  inst_num_of_clauses:                    916
% 3.34/1.02  inst_num_in_passive:                    425
% 3.34/1.02  inst_num_in_active:                     347
% 3.34/1.02  inst_num_in_unprocessed:                144
% 3.34/1.02  inst_num_of_loops:                      440
% 3.34/1.02  inst_num_of_learning_restarts:          0
% 3.34/1.02  inst_num_moves_active_passive:          91
% 3.34/1.02  inst_lit_activity:                      0
% 3.34/1.02  inst_lit_activity_moves:                0
% 3.34/1.02  inst_num_tautologies:                   0
% 3.34/1.02  inst_num_prop_implied:                  0
% 3.34/1.02  inst_num_existing_simplified:           0
% 3.34/1.02  inst_num_eq_res_simplified:             0
% 3.34/1.02  inst_num_child_elim:                    0
% 3.34/1.02  inst_num_of_dismatching_blockings:      646
% 3.34/1.02  inst_num_of_non_proper_insts:           953
% 3.34/1.02  inst_num_of_duplicates:                 0
% 3.34/1.02  inst_inst_num_from_inst_to_res:         0
% 3.34/1.02  inst_dismatching_checking_time:         0.
% 3.34/1.02  
% 3.34/1.02  ------ Resolution
% 3.34/1.02  
% 3.34/1.02  res_num_of_clauses:                     0
% 3.34/1.02  res_num_in_passive:                     0
% 3.34/1.02  res_num_in_active:                      0
% 3.34/1.02  res_num_of_loops:                       161
% 3.34/1.02  res_forward_subset_subsumed:            85
% 3.34/1.02  res_backward_subset_subsumed:           0
% 3.34/1.02  res_forward_subsumed:                   0
% 3.34/1.02  res_backward_subsumed:                  1
% 3.34/1.02  res_forward_subsumption_resolution:     0
% 3.34/1.02  res_backward_subsumption_resolution:    0
% 3.34/1.02  res_clause_to_clause_subsumption:       222
% 3.34/1.02  res_orphan_elimination:                 0
% 3.34/1.02  res_tautology_del:                      107
% 3.34/1.02  res_num_eq_res_simplified:              0
% 3.34/1.02  res_num_sel_changes:                    0
% 3.34/1.02  res_moves_from_active_to_pass:          0
% 3.34/1.02  
% 3.34/1.02  ------ Superposition
% 3.34/1.02  
% 3.34/1.02  sup_time_total:                         0.
% 3.34/1.02  sup_time_generating:                    0.
% 3.34/1.02  sup_time_sim_full:                      0.
% 3.34/1.02  sup_time_sim_immed:                     0.
% 3.34/1.02  
% 3.34/1.02  sup_num_of_clauses:                     73
% 3.34/1.02  sup_num_in_active:                      47
% 3.34/1.02  sup_num_in_passive:                     26
% 3.34/1.02  sup_num_of_loops:                       87
% 3.34/1.02  sup_fw_superposition:                   105
% 3.34/1.02  sup_bw_superposition:                   80
% 3.34/1.02  sup_immediate_simplified:               60
% 3.34/1.02  sup_given_eliminated:                   0
% 3.34/1.02  comparisons_done:                       0
% 3.34/1.02  comparisons_avoided:                    61
% 3.34/1.02  
% 3.34/1.02  ------ Simplifications
% 3.34/1.02  
% 3.34/1.02  
% 3.34/1.02  sim_fw_subset_subsumed:                 15
% 3.34/1.02  sim_bw_subset_subsumed:                 3
% 3.34/1.02  sim_fw_subsumed:                        14
% 3.34/1.02  sim_bw_subsumed:                        0
% 3.34/1.02  sim_fw_subsumption_res:                 0
% 3.34/1.02  sim_bw_subsumption_res:                 0
% 3.34/1.02  sim_tautology_del:                      2
% 3.34/1.02  sim_eq_tautology_del:                   16
% 3.34/1.02  sim_eq_res_simp:                        4
% 3.34/1.02  sim_fw_demodulated:                     16
% 3.34/1.02  sim_bw_demodulated:                     41
% 3.34/1.02  sim_light_normalised:                   36
% 3.34/1.02  sim_joinable_taut:                      0
% 3.34/1.02  sim_joinable_simp:                      0
% 3.34/1.02  sim_ac_normalised:                      0
% 3.34/1.02  sim_smt_subsumption:                    0
% 3.34/1.02  
%------------------------------------------------------------------------------
