%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:04:58 EST 2020

% Result     : Theorem 3.28s
% Output     : CNFRefutation 3.28s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 868 expanded)
%              Number of clauses        :   66 ( 148 expanded)
%              Number of leaves         :   24 ( 228 expanded)
%              Depth                    :   32
%              Number of atoms          :  426 (2199 expanded)
%              Number of equality atoms :  208 (1073 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f110,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f54])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK0(X0,X1),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( r1_tarski(sK0(X0,X1),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK0(X0,X1),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r1_tarski(sK0(X0,X1),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f42])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f111,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f20,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f20])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X4,X3,X2] :
            ( k3_mcart_1(X2,X3,X4) != sK1(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK1(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK1(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f45])).

fof(f81,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f23,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f35,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f36,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f48,plain,
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

fof(f49,plain,
    ( ~ r2_hidden(k1_funct_1(sK4,sK2),sK3)
    & k1_xboole_0 != sK3
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))
    & v1_funct_2(sK4,k1_tarski(sK2),sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f36,f48])).

fof(f93,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) ),
    inference(cnf_transformation,[],[f49])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f12])).

fof(f96,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f65,f66])).

fof(f97,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f64,f96])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f63,f97])).

fof(f99,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f62,f98])).

fof(f100,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f61,f99])).

fof(f101,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f60,f100])).

fof(f107,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) ),
    inference(definition_unfolding,[],[f93,f101])).

fof(f92,plain,(
    v1_funct_2(sK4,k1_tarski(sK2),sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f108,plain,(
    v1_funct_2(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) ),
    inference(definition_unfolding,[],[f92,f101])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
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

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f94,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f49])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 )
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k1_mcart_1(X0) = X1
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( k1_mcart_1(X0) = X1
      | ~ r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)) ) ),
    inference(definition_unfolding,[],[f79,f101])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f33])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f91,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f95,plain,(
    ~ r2_hidden(k1_funct_1(sK4,sK2),sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f16,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f16])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) != X0 ) ),
    inference(definition_unfolding,[],[f71,f57,f101])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f102,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f58,f57])).

cnf(c_6,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1671,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_1668,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_25,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1658,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_476,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(X2)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_35])).

cnf(c_477,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(X1) ),
    inference(unflattening,[status(thm)],[c_476])).

cnf(c_1656,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(X0)
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X1,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_477])).

cnf(c_36,negated_conjecture,
    ( v1_funct_2(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_31,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_491,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_35])).

cnf(c_492,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | k1_relset_1(X0,X1,sK4) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_491])).

cnf(c_719,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != X0
    | k1_relset_1(X0,X1,sK4) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK3 != X1
    | sK4 != sK4
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_492])).

cnf(c_720,plain,
    ( k1_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_719])).

cnf(c_34,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_721,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))
    | k1_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_720,c_34])).

cnf(c_722,plain,
    ( k1_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) ),
    inference(renaming,[status(thm)],[c_721])).

cnf(c_834,plain,
    ( k1_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(equality_resolution_simp,[status(thm)],[c_722])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_527,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_35])).

cnf(c_528,plain,
    ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_527])).

cnf(c_1893,plain,
    ( k1_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4) = k1_relat_1(sK4) ),
    inference(equality_resolution,[status(thm)],[c_528])).

cnf(c_2028,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_relat_1(sK4) ),
    inference(light_normalisation,[status(thm)],[c_834,c_1893])).

cnf(c_2301,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3)) != k1_zfmisc_1(X0)
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X1,sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1656,c_2028])).

cnf(c_2308,plain,
    ( r2_hidden(X0,k2_zfmisc_1(k1_relat_1(sK4),sK3)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2301])).

cnf(c_22,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2))
    | k1_mcart_1(X0) = X1 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1661,plain,
    ( k1_mcart_1(X0) = X1
    | r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3536,plain,
    ( k1_mcart_1(X0) = sK2
    | r2_hidden(X0,k2_zfmisc_1(k1_relat_1(sK4),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2028,c_1661])).

cnf(c_3903,plain,
    ( k1_mcart_1(X0) = sK2
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2308,c_3536])).

cnf(c_3929,plain,
    ( k1_mcart_1(sK1(sK4)) = sK2
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1658,c_3903])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k1_mcart_1(X0),X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1663,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3112,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(k1_mcart_1(X0),k1_relat_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2308,c_1663])).

cnf(c_4451,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK1(sK4),sK4) != iProver_top
    | r2_hidden(sK2,k1_relat_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3929,c_3112])).

cnf(c_32,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_449,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_37])).

cnf(c_450,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(k1_funct_1(sK4,X2),X1)
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_449])).

cnf(c_601,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(k1_funct_1(sK4,X2),X1)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK4 != sK4
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_35,c_450])).

cnf(c_698,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k1_funct_1(sK4,X0),X2)
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != X1
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK3 != X2
    | sK4 != sK4
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_601])).

cnf(c_699,plain,
    ( ~ r2_hidden(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | r2_hidden(k1_funct_1(sK4,X0),sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_698])).

cnf(c_703,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))
    | r2_hidden(k1_funct_1(sK4,X0),sK3)
    | ~ r2_hidden(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_699,c_34])).

cnf(c_704,plain,
    ( ~ r2_hidden(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | r2_hidden(k1_funct_1(sK4,X0),sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) ),
    inference(renaming,[status(thm)],[c_703])).

cnf(c_835,plain,
    ( ~ r2_hidden(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | r2_hidden(k1_funct_1(sK4,X0),sK3) ),
    inference(equality_resolution_simp,[status(thm)],[c_704])).

cnf(c_1654,plain,
    ( r2_hidden(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_835])).

cnf(c_2450,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1654,c_2028])).

cnf(c_33,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(sK4,sK2),sK3) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1657,plain,
    ( r2_hidden(k1_funct_1(sK4,sK2),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_2456,plain,
    ( r2_hidden(sK2,k1_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2450,c_1657])).

cnf(c_4454,plain,
    ( r2_hidden(sK1(sK4),sK4) != iProver_top
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4451,c_2456])).

cnf(c_4455,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK1(sK4),sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_4454])).

cnf(c_4460,plain,
    ( sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1658,c_4455])).

cnf(c_7246,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_4460,c_2028])).

cnf(c_17,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_7251,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7246,c_17])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | k5_xboole_0(X1,k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) != X1 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1665,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) != X0
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_7339,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) != X0
    | r2_hidden(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7251,c_1665])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_7343,plain,
    ( X0 != X0
    | r2_hidden(sK2,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7339,c_7])).

cnf(c_7344,plain,
    ( r2_hidden(sK2,X0) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_7343])).

cnf(c_9066,plain,
    ( r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1668,c_7344])).

cnf(c_9197,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_1671,c_9066])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:43:44 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.28/1.04  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.04  
% 3.28/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.28/1.04  
% 3.28/1.04  ------  iProver source info
% 3.28/1.04  
% 3.28/1.04  git: date: 2020-06-30 10:37:57 +0100
% 3.28/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.28/1.04  git: non_committed_changes: false
% 3.28/1.04  git: last_make_outside_of_git: false
% 3.28/1.04  
% 3.28/1.04  ------ 
% 3.28/1.04  
% 3.28/1.04  ------ Input Options
% 3.28/1.04  
% 3.28/1.04  --out_options                           all
% 3.28/1.04  --tptp_safe_out                         true
% 3.28/1.04  --problem_path                          ""
% 3.28/1.04  --include_path                          ""
% 3.28/1.04  --clausifier                            res/vclausify_rel
% 3.28/1.04  --clausifier_options                    --mode clausify
% 3.28/1.04  --stdin                                 false
% 3.28/1.04  --stats_out                             all
% 3.28/1.04  
% 3.28/1.04  ------ General Options
% 3.28/1.04  
% 3.28/1.04  --fof                                   false
% 3.28/1.04  --time_out_real                         305.
% 3.28/1.04  --time_out_virtual                      -1.
% 3.28/1.04  --symbol_type_check                     false
% 3.28/1.04  --clausify_out                          false
% 3.28/1.04  --sig_cnt_out                           false
% 3.28/1.04  --trig_cnt_out                          false
% 3.28/1.04  --trig_cnt_out_tolerance                1.
% 3.28/1.04  --trig_cnt_out_sk_spl                   false
% 3.28/1.04  --abstr_cl_out                          false
% 3.28/1.04  
% 3.28/1.04  ------ Global Options
% 3.28/1.04  
% 3.28/1.04  --schedule                              default
% 3.28/1.04  --add_important_lit                     false
% 3.28/1.04  --prop_solver_per_cl                    1000
% 3.28/1.04  --min_unsat_core                        false
% 3.28/1.04  --soft_assumptions                      false
% 3.28/1.04  --soft_lemma_size                       3
% 3.28/1.04  --prop_impl_unit_size                   0
% 3.28/1.04  --prop_impl_unit                        []
% 3.28/1.04  --share_sel_clauses                     true
% 3.28/1.04  --reset_solvers                         false
% 3.28/1.04  --bc_imp_inh                            [conj_cone]
% 3.28/1.04  --conj_cone_tolerance                   3.
% 3.28/1.04  --extra_neg_conj                        none
% 3.28/1.04  --large_theory_mode                     true
% 3.28/1.04  --prolific_symb_bound                   200
% 3.28/1.04  --lt_threshold                          2000
% 3.28/1.04  --clause_weak_htbl                      true
% 3.28/1.04  --gc_record_bc_elim                     false
% 3.28/1.04  
% 3.28/1.04  ------ Preprocessing Options
% 3.28/1.04  
% 3.28/1.04  --preprocessing_flag                    true
% 3.28/1.04  --time_out_prep_mult                    0.1
% 3.28/1.04  --splitting_mode                        input
% 3.28/1.04  --splitting_grd                         true
% 3.28/1.04  --splitting_cvd                         false
% 3.28/1.04  --splitting_cvd_svl                     false
% 3.28/1.04  --splitting_nvd                         32
% 3.28/1.04  --sub_typing                            true
% 3.28/1.04  --prep_gs_sim                           true
% 3.28/1.04  --prep_unflatten                        true
% 3.28/1.04  --prep_res_sim                          true
% 3.28/1.04  --prep_upred                            true
% 3.28/1.04  --prep_sem_filter                       exhaustive
% 3.28/1.04  --prep_sem_filter_out                   false
% 3.28/1.04  --pred_elim                             true
% 3.28/1.04  --res_sim_input                         true
% 3.28/1.04  --eq_ax_congr_red                       true
% 3.28/1.04  --pure_diseq_elim                       true
% 3.28/1.04  --brand_transform                       false
% 3.28/1.04  --non_eq_to_eq                          false
% 3.28/1.04  --prep_def_merge                        true
% 3.28/1.04  --prep_def_merge_prop_impl              false
% 3.28/1.04  --prep_def_merge_mbd                    true
% 3.28/1.04  --prep_def_merge_tr_red                 false
% 3.28/1.04  --prep_def_merge_tr_cl                  false
% 3.28/1.04  --smt_preprocessing                     true
% 3.28/1.04  --smt_ac_axioms                         fast
% 3.28/1.04  --preprocessed_out                      false
% 3.28/1.04  --preprocessed_stats                    false
% 3.28/1.04  
% 3.28/1.04  ------ Abstraction refinement Options
% 3.28/1.04  
% 3.28/1.04  --abstr_ref                             []
% 3.28/1.04  --abstr_ref_prep                        false
% 3.28/1.04  --abstr_ref_until_sat                   false
% 3.28/1.04  --abstr_ref_sig_restrict                funpre
% 3.28/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 3.28/1.04  --abstr_ref_under                       []
% 3.28/1.04  
% 3.28/1.04  ------ SAT Options
% 3.28/1.04  
% 3.28/1.04  --sat_mode                              false
% 3.28/1.04  --sat_fm_restart_options                ""
% 3.28/1.04  --sat_gr_def                            false
% 3.28/1.04  --sat_epr_types                         true
% 3.28/1.04  --sat_non_cyclic_types                  false
% 3.28/1.04  --sat_finite_models                     false
% 3.28/1.04  --sat_fm_lemmas                         false
% 3.28/1.04  --sat_fm_prep                           false
% 3.28/1.04  --sat_fm_uc_incr                        true
% 3.28/1.04  --sat_out_model                         small
% 3.28/1.04  --sat_out_clauses                       false
% 3.28/1.04  
% 3.28/1.04  ------ QBF Options
% 3.28/1.04  
% 3.28/1.04  --qbf_mode                              false
% 3.28/1.04  --qbf_elim_univ                         false
% 3.28/1.04  --qbf_dom_inst                          none
% 3.28/1.04  --qbf_dom_pre_inst                      false
% 3.28/1.04  --qbf_sk_in                             false
% 3.28/1.04  --qbf_pred_elim                         true
% 3.28/1.04  --qbf_split                             512
% 3.28/1.04  
% 3.28/1.04  ------ BMC1 Options
% 3.28/1.04  
% 3.28/1.04  --bmc1_incremental                      false
% 3.28/1.04  --bmc1_axioms                           reachable_all
% 3.28/1.04  --bmc1_min_bound                        0
% 3.28/1.04  --bmc1_max_bound                        -1
% 3.28/1.04  --bmc1_max_bound_default                -1
% 3.28/1.04  --bmc1_symbol_reachability              true
% 3.28/1.04  --bmc1_property_lemmas                  false
% 3.28/1.04  --bmc1_k_induction                      false
% 3.28/1.04  --bmc1_non_equiv_states                 false
% 3.28/1.04  --bmc1_deadlock                         false
% 3.28/1.04  --bmc1_ucm                              false
% 3.28/1.04  --bmc1_add_unsat_core                   none
% 3.28/1.04  --bmc1_unsat_core_children              false
% 3.28/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 3.28/1.04  --bmc1_out_stat                         full
% 3.28/1.04  --bmc1_ground_init                      false
% 3.28/1.04  --bmc1_pre_inst_next_state              false
% 3.28/1.04  --bmc1_pre_inst_state                   false
% 3.28/1.04  --bmc1_pre_inst_reach_state             false
% 3.28/1.04  --bmc1_out_unsat_core                   false
% 3.28/1.04  --bmc1_aig_witness_out                  false
% 3.28/1.04  --bmc1_verbose                          false
% 3.28/1.04  --bmc1_dump_clauses_tptp                false
% 3.28/1.04  --bmc1_dump_unsat_core_tptp             false
% 3.28/1.04  --bmc1_dump_file                        -
% 3.28/1.04  --bmc1_ucm_expand_uc_limit              128
% 3.28/1.04  --bmc1_ucm_n_expand_iterations          6
% 3.28/1.04  --bmc1_ucm_extend_mode                  1
% 3.28/1.04  --bmc1_ucm_init_mode                    2
% 3.28/1.04  --bmc1_ucm_cone_mode                    none
% 3.28/1.04  --bmc1_ucm_reduced_relation_type        0
% 3.28/1.04  --bmc1_ucm_relax_model                  4
% 3.28/1.04  --bmc1_ucm_full_tr_after_sat            true
% 3.28/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 3.28/1.04  --bmc1_ucm_layered_model                none
% 3.28/1.04  --bmc1_ucm_max_lemma_size               10
% 3.28/1.04  
% 3.28/1.04  ------ AIG Options
% 3.28/1.04  
% 3.28/1.04  --aig_mode                              false
% 3.28/1.04  
% 3.28/1.04  ------ Instantiation Options
% 3.28/1.04  
% 3.28/1.04  --instantiation_flag                    true
% 3.28/1.04  --inst_sos_flag                         false
% 3.28/1.04  --inst_sos_phase                        true
% 3.28/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.28/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.28/1.04  --inst_lit_sel_side                     num_symb
% 3.28/1.04  --inst_solver_per_active                1400
% 3.28/1.04  --inst_solver_calls_frac                1.
% 3.28/1.04  --inst_passive_queue_type               priority_queues
% 3.28/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.28/1.04  --inst_passive_queues_freq              [25;2]
% 3.28/1.04  --inst_dismatching                      true
% 3.28/1.04  --inst_eager_unprocessed_to_passive     true
% 3.28/1.04  --inst_prop_sim_given                   true
% 3.28/1.04  --inst_prop_sim_new                     false
% 3.28/1.04  --inst_subs_new                         false
% 3.28/1.04  --inst_eq_res_simp                      false
% 3.28/1.04  --inst_subs_given                       false
% 3.28/1.04  --inst_orphan_elimination               true
% 3.28/1.04  --inst_learning_loop_flag               true
% 3.28/1.04  --inst_learning_start                   3000
% 3.28/1.04  --inst_learning_factor                  2
% 3.28/1.04  --inst_start_prop_sim_after_learn       3
% 3.28/1.04  --inst_sel_renew                        solver
% 3.28/1.04  --inst_lit_activity_flag                true
% 3.28/1.04  --inst_restr_to_given                   false
% 3.28/1.04  --inst_activity_threshold               500
% 3.28/1.04  --inst_out_proof                        true
% 3.28/1.04  
% 3.28/1.04  ------ Resolution Options
% 3.28/1.04  
% 3.28/1.04  --resolution_flag                       true
% 3.28/1.04  --res_lit_sel                           adaptive
% 3.28/1.04  --res_lit_sel_side                      none
% 3.28/1.04  --res_ordering                          kbo
% 3.28/1.04  --res_to_prop_solver                    active
% 3.28/1.04  --res_prop_simpl_new                    false
% 3.28/1.04  --res_prop_simpl_given                  true
% 3.28/1.04  --res_passive_queue_type                priority_queues
% 3.28/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.28/1.04  --res_passive_queues_freq               [15;5]
% 3.28/1.04  --res_forward_subs                      full
% 3.28/1.04  --res_backward_subs                     full
% 3.28/1.04  --res_forward_subs_resolution           true
% 3.28/1.04  --res_backward_subs_resolution          true
% 3.28/1.04  --res_orphan_elimination                true
% 3.28/1.04  --res_time_limit                        2.
% 3.28/1.04  --res_out_proof                         true
% 3.28/1.04  
% 3.28/1.04  ------ Superposition Options
% 3.28/1.04  
% 3.28/1.04  --superposition_flag                    true
% 3.28/1.04  --sup_passive_queue_type                priority_queues
% 3.28/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.28/1.04  --sup_passive_queues_freq               [8;1;4]
% 3.28/1.04  --demod_completeness_check              fast
% 3.28/1.04  --demod_use_ground                      true
% 3.28/1.04  --sup_to_prop_solver                    passive
% 3.28/1.04  --sup_prop_simpl_new                    true
% 3.28/1.04  --sup_prop_simpl_given                  true
% 3.28/1.04  --sup_fun_splitting                     false
% 3.28/1.04  --sup_smt_interval                      50000
% 3.28/1.04  
% 3.28/1.04  ------ Superposition Simplification Setup
% 3.28/1.04  
% 3.28/1.04  --sup_indices_passive                   []
% 3.28/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.28/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.28/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.28/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 3.28/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.28/1.04  --sup_full_bw                           [BwDemod]
% 3.28/1.04  --sup_immed_triv                        [TrivRules]
% 3.28/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.28/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.28/1.04  --sup_immed_bw_main                     []
% 3.28/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.28/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 3.28/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.28/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.28/1.04  
% 3.28/1.04  ------ Combination Options
% 3.28/1.04  
% 3.28/1.04  --comb_res_mult                         3
% 3.28/1.04  --comb_sup_mult                         2
% 3.28/1.04  --comb_inst_mult                        10
% 3.28/1.04  
% 3.28/1.04  ------ Debug Options
% 3.28/1.04  
% 3.28/1.04  --dbg_backtrace                         false
% 3.28/1.04  --dbg_dump_prop_clauses                 false
% 3.28/1.04  --dbg_dump_prop_clauses_file            -
% 3.28/1.04  --dbg_out_stat                          false
% 3.28/1.04  ------ Parsing...
% 3.28/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.28/1.04  
% 3.28/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.28/1.04  
% 3.28/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.28/1.04  
% 3.28/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.28/1.04  ------ Proving...
% 3.28/1.04  ------ Problem Properties 
% 3.28/1.04  
% 3.28/1.04  
% 3.28/1.04  clauses                                 33
% 3.28/1.04  conjectures                             2
% 3.28/1.04  EPR                                     3
% 3.28/1.04  Horn                                    24
% 3.28/1.04  unary                                   8
% 3.28/1.04  binary                                  11
% 3.28/1.04  lits                                    77
% 3.28/1.04  lits eq                                 33
% 3.28/1.04  fd_pure                                 0
% 3.28/1.04  fd_pseudo                               0
% 3.28/1.04  fd_cond                                 5
% 3.28/1.04  fd_pseudo_cond                          4
% 3.28/1.04  AC symbols                              0
% 3.28/1.04  
% 3.28/1.04  ------ Schedule dynamic 5 is on 
% 3.28/1.04  
% 3.28/1.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.28/1.04  
% 3.28/1.04  
% 3.28/1.04  ------ 
% 3.28/1.04  Current options:
% 3.28/1.04  ------ 
% 3.28/1.04  
% 3.28/1.04  ------ Input Options
% 3.28/1.04  
% 3.28/1.04  --out_options                           all
% 3.28/1.04  --tptp_safe_out                         true
% 3.28/1.04  --problem_path                          ""
% 3.28/1.04  --include_path                          ""
% 3.28/1.04  --clausifier                            res/vclausify_rel
% 3.28/1.04  --clausifier_options                    --mode clausify
% 3.28/1.04  --stdin                                 false
% 3.28/1.04  --stats_out                             all
% 3.28/1.04  
% 3.28/1.04  ------ General Options
% 3.28/1.04  
% 3.28/1.04  --fof                                   false
% 3.28/1.04  --time_out_real                         305.
% 3.28/1.04  --time_out_virtual                      -1.
% 3.28/1.04  --symbol_type_check                     false
% 3.28/1.04  --clausify_out                          false
% 3.28/1.04  --sig_cnt_out                           false
% 3.28/1.04  --trig_cnt_out                          false
% 3.28/1.04  --trig_cnt_out_tolerance                1.
% 3.28/1.04  --trig_cnt_out_sk_spl                   false
% 3.28/1.04  --abstr_cl_out                          false
% 3.28/1.04  
% 3.28/1.04  ------ Global Options
% 3.28/1.04  
% 3.28/1.04  --schedule                              default
% 3.28/1.04  --add_important_lit                     false
% 3.28/1.04  --prop_solver_per_cl                    1000
% 3.28/1.04  --min_unsat_core                        false
% 3.28/1.04  --soft_assumptions                      false
% 3.28/1.04  --soft_lemma_size                       3
% 3.28/1.04  --prop_impl_unit_size                   0
% 3.28/1.04  --prop_impl_unit                        []
% 3.28/1.04  --share_sel_clauses                     true
% 3.28/1.04  --reset_solvers                         false
% 3.28/1.04  --bc_imp_inh                            [conj_cone]
% 3.28/1.04  --conj_cone_tolerance                   3.
% 3.28/1.04  --extra_neg_conj                        none
% 3.28/1.04  --large_theory_mode                     true
% 3.28/1.04  --prolific_symb_bound                   200
% 3.28/1.04  --lt_threshold                          2000
% 3.28/1.04  --clause_weak_htbl                      true
% 3.28/1.04  --gc_record_bc_elim                     false
% 3.28/1.04  
% 3.28/1.04  ------ Preprocessing Options
% 3.28/1.04  
% 3.28/1.04  --preprocessing_flag                    true
% 3.28/1.04  --time_out_prep_mult                    0.1
% 3.28/1.04  --splitting_mode                        input
% 3.28/1.04  --splitting_grd                         true
% 3.28/1.04  --splitting_cvd                         false
% 3.28/1.04  --splitting_cvd_svl                     false
% 3.28/1.04  --splitting_nvd                         32
% 3.28/1.04  --sub_typing                            true
% 3.28/1.04  --prep_gs_sim                           true
% 3.28/1.04  --prep_unflatten                        true
% 3.28/1.04  --prep_res_sim                          true
% 3.28/1.04  --prep_upred                            true
% 3.28/1.04  --prep_sem_filter                       exhaustive
% 3.28/1.04  --prep_sem_filter_out                   false
% 3.28/1.04  --pred_elim                             true
% 3.28/1.04  --res_sim_input                         true
% 3.28/1.04  --eq_ax_congr_red                       true
% 3.28/1.04  --pure_diseq_elim                       true
% 3.28/1.04  --brand_transform                       false
% 3.28/1.04  --non_eq_to_eq                          false
% 3.28/1.04  --prep_def_merge                        true
% 3.28/1.04  --prep_def_merge_prop_impl              false
% 3.28/1.04  --prep_def_merge_mbd                    true
% 3.28/1.04  --prep_def_merge_tr_red                 false
% 3.28/1.04  --prep_def_merge_tr_cl                  false
% 3.28/1.04  --smt_preprocessing                     true
% 3.28/1.04  --smt_ac_axioms                         fast
% 3.28/1.04  --preprocessed_out                      false
% 3.28/1.04  --preprocessed_stats                    false
% 3.28/1.04  
% 3.28/1.04  ------ Abstraction refinement Options
% 3.28/1.04  
% 3.28/1.04  --abstr_ref                             []
% 3.28/1.04  --abstr_ref_prep                        false
% 3.28/1.04  --abstr_ref_until_sat                   false
% 3.28/1.04  --abstr_ref_sig_restrict                funpre
% 3.28/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 3.28/1.04  --abstr_ref_under                       []
% 3.28/1.04  
% 3.28/1.04  ------ SAT Options
% 3.28/1.04  
% 3.28/1.04  --sat_mode                              false
% 3.28/1.04  --sat_fm_restart_options                ""
% 3.28/1.04  --sat_gr_def                            false
% 3.28/1.04  --sat_epr_types                         true
% 3.28/1.04  --sat_non_cyclic_types                  false
% 3.28/1.04  --sat_finite_models                     false
% 3.28/1.04  --sat_fm_lemmas                         false
% 3.28/1.04  --sat_fm_prep                           false
% 3.28/1.04  --sat_fm_uc_incr                        true
% 3.28/1.04  --sat_out_model                         small
% 3.28/1.04  --sat_out_clauses                       false
% 3.28/1.04  
% 3.28/1.04  ------ QBF Options
% 3.28/1.04  
% 3.28/1.04  --qbf_mode                              false
% 3.28/1.04  --qbf_elim_univ                         false
% 3.28/1.04  --qbf_dom_inst                          none
% 3.28/1.04  --qbf_dom_pre_inst                      false
% 3.28/1.04  --qbf_sk_in                             false
% 3.28/1.04  --qbf_pred_elim                         true
% 3.28/1.04  --qbf_split                             512
% 3.28/1.04  
% 3.28/1.04  ------ BMC1 Options
% 3.28/1.04  
% 3.28/1.04  --bmc1_incremental                      false
% 3.28/1.04  --bmc1_axioms                           reachable_all
% 3.28/1.04  --bmc1_min_bound                        0
% 3.28/1.04  --bmc1_max_bound                        -1
% 3.28/1.04  --bmc1_max_bound_default                -1
% 3.28/1.04  --bmc1_symbol_reachability              true
% 3.28/1.04  --bmc1_property_lemmas                  false
% 3.28/1.04  --bmc1_k_induction                      false
% 3.28/1.04  --bmc1_non_equiv_states                 false
% 3.28/1.04  --bmc1_deadlock                         false
% 3.28/1.04  --bmc1_ucm                              false
% 3.28/1.04  --bmc1_add_unsat_core                   none
% 3.28/1.04  --bmc1_unsat_core_children              false
% 3.28/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 3.28/1.04  --bmc1_out_stat                         full
% 3.28/1.04  --bmc1_ground_init                      false
% 3.28/1.04  --bmc1_pre_inst_next_state              false
% 3.28/1.04  --bmc1_pre_inst_state                   false
% 3.28/1.04  --bmc1_pre_inst_reach_state             false
% 3.28/1.04  --bmc1_out_unsat_core                   false
% 3.28/1.04  --bmc1_aig_witness_out                  false
% 3.28/1.04  --bmc1_verbose                          false
% 3.28/1.04  --bmc1_dump_clauses_tptp                false
% 3.28/1.04  --bmc1_dump_unsat_core_tptp             false
% 3.28/1.04  --bmc1_dump_file                        -
% 3.28/1.04  --bmc1_ucm_expand_uc_limit              128
% 3.28/1.04  --bmc1_ucm_n_expand_iterations          6
% 3.28/1.04  --bmc1_ucm_extend_mode                  1
% 3.28/1.04  --bmc1_ucm_init_mode                    2
% 3.28/1.04  --bmc1_ucm_cone_mode                    none
% 3.28/1.04  --bmc1_ucm_reduced_relation_type        0
% 3.28/1.04  --bmc1_ucm_relax_model                  4
% 3.28/1.04  --bmc1_ucm_full_tr_after_sat            true
% 3.28/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 3.28/1.04  --bmc1_ucm_layered_model                none
% 3.28/1.04  --bmc1_ucm_max_lemma_size               10
% 3.28/1.04  
% 3.28/1.04  ------ AIG Options
% 3.28/1.04  
% 3.28/1.04  --aig_mode                              false
% 3.28/1.04  
% 3.28/1.04  ------ Instantiation Options
% 3.28/1.04  
% 3.28/1.04  --instantiation_flag                    true
% 3.28/1.04  --inst_sos_flag                         false
% 3.28/1.04  --inst_sos_phase                        true
% 3.28/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.28/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.28/1.04  --inst_lit_sel_side                     none
% 3.28/1.04  --inst_solver_per_active                1400
% 3.28/1.04  --inst_solver_calls_frac                1.
% 3.28/1.04  --inst_passive_queue_type               priority_queues
% 3.28/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.28/1.04  --inst_passive_queues_freq              [25;2]
% 3.28/1.04  --inst_dismatching                      true
% 3.28/1.04  --inst_eager_unprocessed_to_passive     true
% 3.28/1.04  --inst_prop_sim_given                   true
% 3.28/1.04  --inst_prop_sim_new                     false
% 3.28/1.04  --inst_subs_new                         false
% 3.28/1.04  --inst_eq_res_simp                      false
% 3.28/1.04  --inst_subs_given                       false
% 3.28/1.04  --inst_orphan_elimination               true
% 3.28/1.04  --inst_learning_loop_flag               true
% 3.28/1.04  --inst_learning_start                   3000
% 3.28/1.04  --inst_learning_factor                  2
% 3.28/1.04  --inst_start_prop_sim_after_learn       3
% 3.28/1.04  --inst_sel_renew                        solver
% 3.28/1.04  --inst_lit_activity_flag                true
% 3.28/1.04  --inst_restr_to_given                   false
% 3.28/1.04  --inst_activity_threshold               500
% 3.28/1.04  --inst_out_proof                        true
% 3.28/1.04  
% 3.28/1.04  ------ Resolution Options
% 3.28/1.04  
% 3.28/1.04  --resolution_flag                       false
% 3.28/1.04  --res_lit_sel                           adaptive
% 3.28/1.04  --res_lit_sel_side                      none
% 3.28/1.04  --res_ordering                          kbo
% 3.28/1.04  --res_to_prop_solver                    active
% 3.28/1.04  --res_prop_simpl_new                    false
% 3.28/1.04  --res_prop_simpl_given                  true
% 3.28/1.04  --res_passive_queue_type                priority_queues
% 3.28/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.28/1.04  --res_passive_queues_freq               [15;5]
% 3.28/1.04  --res_forward_subs                      full
% 3.28/1.04  --res_backward_subs                     full
% 3.28/1.04  --res_forward_subs_resolution           true
% 3.28/1.04  --res_backward_subs_resolution          true
% 3.28/1.04  --res_orphan_elimination                true
% 3.28/1.04  --res_time_limit                        2.
% 3.28/1.04  --res_out_proof                         true
% 3.28/1.04  
% 3.28/1.04  ------ Superposition Options
% 3.28/1.04  
% 3.28/1.04  --superposition_flag                    true
% 3.28/1.04  --sup_passive_queue_type                priority_queues
% 3.28/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.28/1.04  --sup_passive_queues_freq               [8;1;4]
% 3.28/1.04  --demod_completeness_check              fast
% 3.28/1.04  --demod_use_ground                      true
% 3.28/1.04  --sup_to_prop_solver                    passive
% 3.28/1.04  --sup_prop_simpl_new                    true
% 3.28/1.04  --sup_prop_simpl_given                  true
% 3.28/1.04  --sup_fun_splitting                     false
% 3.28/1.04  --sup_smt_interval                      50000
% 3.28/1.04  
% 3.28/1.04  ------ Superposition Simplification Setup
% 3.28/1.04  
% 3.28/1.04  --sup_indices_passive                   []
% 3.28/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.28/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.28/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.28/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 3.28/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.28/1.04  --sup_full_bw                           [BwDemod]
% 3.28/1.04  --sup_immed_triv                        [TrivRules]
% 3.28/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.28/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.28/1.04  --sup_immed_bw_main                     []
% 3.28/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.28/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 3.28/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.28/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.28/1.04  
% 3.28/1.04  ------ Combination Options
% 3.28/1.04  
% 3.28/1.04  --comb_res_mult                         3
% 3.28/1.04  --comb_sup_mult                         2
% 3.28/1.04  --comb_inst_mult                        10
% 3.28/1.04  
% 3.28/1.04  ------ Debug Options
% 3.28/1.04  
% 3.28/1.04  --dbg_backtrace                         false
% 3.28/1.04  --dbg_dump_prop_clauses                 false
% 3.28/1.04  --dbg_dump_prop_clauses_file            -
% 3.28/1.04  --dbg_out_stat                          false
% 3.28/1.04  
% 3.28/1.04  
% 3.28/1.04  
% 3.28/1.04  
% 3.28/1.04  ------ Proving...
% 3.28/1.04  
% 3.28/1.04  
% 3.28/1.04  % SZS status Theorem for theBenchmark.p
% 3.28/1.04  
% 3.28/1.04   Resolution empty clause
% 3.28/1.04  
% 3.28/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 3.28/1.04  
% 3.28/1.04  fof(f2,axiom,(
% 3.28/1.04    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.28/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/1.04  
% 3.28/1.04  fof(f38,plain,(
% 3.28/1.04    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.28/1.04    inference(nnf_transformation,[],[f2])).
% 3.28/1.04  
% 3.28/1.04  fof(f39,plain,(
% 3.28/1.04    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.28/1.04    inference(flattening,[],[f38])).
% 3.28/1.04  
% 3.28/1.04  fof(f54,plain,(
% 3.28/1.04    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.28/1.04    inference(cnf_transformation,[],[f39])).
% 3.28/1.04  
% 3.28/1.04  fof(f110,plain,(
% 3.28/1.04    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.28/1.04    inference(equality_resolution,[],[f54])).
% 3.28/1.04  
% 3.28/1.04  fof(f13,axiom,(
% 3.28/1.04    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 3.28/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/1.04  
% 3.28/1.04  fof(f40,plain,(
% 3.28/1.04    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.28/1.04    inference(nnf_transformation,[],[f13])).
% 3.28/1.04  
% 3.28/1.04  fof(f41,plain,(
% 3.28/1.04    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.28/1.04    inference(rectify,[],[f40])).
% 3.28/1.04  
% 3.28/1.04  fof(f42,plain,(
% 3.28/1.04    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 3.28/1.04    introduced(choice_axiom,[])).
% 3.28/1.04  
% 3.28/1.04  fof(f43,plain,(
% 3.28/1.04    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.28/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f42])).
% 3.28/1.04  
% 3.28/1.04  fof(f68,plain,(
% 3.28/1.04    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 3.28/1.04    inference(cnf_transformation,[],[f43])).
% 3.28/1.04  
% 3.28/1.04  fof(f111,plain,(
% 3.28/1.04    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 3.28/1.04    inference(equality_resolution,[],[f68])).
% 3.28/1.04  
% 3.28/1.04  fof(f20,axiom,(
% 3.28/1.04    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 3.28/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/1.04  
% 3.28/1.04  fof(f30,plain,(
% 3.28/1.04    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 3.28/1.04    inference(ennf_transformation,[],[f20])).
% 3.28/1.04  
% 3.28/1.04  fof(f45,plain,(
% 3.28/1.04    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK1(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK1(X0),X0)))),
% 3.28/1.04    introduced(choice_axiom,[])).
% 3.28/1.04  
% 3.28/1.04  fof(f46,plain,(
% 3.28/1.04    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK1(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK1(X0),X0)) | k1_xboole_0 = X0)),
% 3.28/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f45])).
% 3.28/1.04  
% 3.28/1.04  fof(f81,plain,(
% 3.28/1.04    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 3.28/1.04    inference(cnf_transformation,[],[f46])).
% 3.28/1.04  
% 3.28/1.04  fof(f15,axiom,(
% 3.28/1.04    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.28/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/1.04  
% 3.28/1.04  fof(f26,plain,(
% 3.28/1.04    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.28/1.04    inference(ennf_transformation,[],[f15])).
% 3.28/1.04  
% 3.28/1.04  fof(f73,plain,(
% 3.28/1.04    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.28/1.04    inference(cnf_transformation,[],[f26])).
% 3.28/1.04  
% 3.28/1.04  fof(f23,conjecture,(
% 3.28/1.04    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 3.28/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/1.04  
% 3.28/1.04  fof(f24,negated_conjecture,(
% 3.28/1.04    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 3.28/1.04    inference(negated_conjecture,[],[f23])).
% 3.28/1.04  
% 3.28/1.04  fof(f35,plain,(
% 3.28/1.04    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 3.28/1.04    inference(ennf_transformation,[],[f24])).
% 3.28/1.04  
% 3.28/1.04  fof(f36,plain,(
% 3.28/1.04    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 3.28/1.04    inference(flattening,[],[f35])).
% 3.28/1.04  
% 3.28/1.04  fof(f48,plain,(
% 3.28/1.04    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (~r2_hidden(k1_funct_1(sK4,sK2),sK3) & k1_xboole_0 != sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) & v1_funct_2(sK4,k1_tarski(sK2),sK3) & v1_funct_1(sK4))),
% 3.28/1.04    introduced(choice_axiom,[])).
% 3.28/1.04  
% 3.28/1.04  fof(f49,plain,(
% 3.28/1.04    ~r2_hidden(k1_funct_1(sK4,sK2),sK3) & k1_xboole_0 != sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) & v1_funct_2(sK4,k1_tarski(sK2),sK3) & v1_funct_1(sK4)),
% 3.28/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f36,f48])).
% 3.28/1.04  
% 3.28/1.04  fof(f93,plain,(
% 3.28/1.04    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))),
% 3.28/1.04    inference(cnf_transformation,[],[f49])).
% 3.28/1.04  
% 3.28/1.04  fof(f6,axiom,(
% 3.28/1.04    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.28/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/1.04  
% 3.28/1.04  fof(f60,plain,(
% 3.28/1.04    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.28/1.04    inference(cnf_transformation,[],[f6])).
% 3.28/1.04  
% 3.28/1.04  fof(f7,axiom,(
% 3.28/1.04    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.28/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/1.04  
% 3.28/1.04  fof(f61,plain,(
% 3.28/1.04    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.28/1.04    inference(cnf_transformation,[],[f7])).
% 3.28/1.04  
% 3.28/1.04  fof(f8,axiom,(
% 3.28/1.04    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.28/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/1.04  
% 3.28/1.04  fof(f62,plain,(
% 3.28/1.04    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.28/1.04    inference(cnf_transformation,[],[f8])).
% 3.28/1.04  
% 3.28/1.04  fof(f9,axiom,(
% 3.28/1.04    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.28/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/1.04  
% 3.28/1.04  fof(f63,plain,(
% 3.28/1.04    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.28/1.04    inference(cnf_transformation,[],[f9])).
% 3.28/1.04  
% 3.28/1.04  fof(f10,axiom,(
% 3.28/1.04    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.28/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/1.04  
% 3.28/1.04  fof(f64,plain,(
% 3.28/1.04    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.28/1.04    inference(cnf_transformation,[],[f10])).
% 3.28/1.04  
% 3.28/1.04  fof(f11,axiom,(
% 3.28/1.04    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.28/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/1.04  
% 3.28/1.04  fof(f65,plain,(
% 3.28/1.04    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.28/1.04    inference(cnf_transformation,[],[f11])).
% 3.28/1.04  
% 3.28/1.04  fof(f12,axiom,(
% 3.28/1.04    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.28/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/1.04  
% 3.28/1.04  fof(f66,plain,(
% 3.28/1.04    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.28/1.04    inference(cnf_transformation,[],[f12])).
% 3.28/1.04  
% 3.28/1.04  fof(f96,plain,(
% 3.28/1.04    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.28/1.04    inference(definition_unfolding,[],[f65,f66])).
% 3.28/1.04  
% 3.28/1.04  fof(f97,plain,(
% 3.28/1.04    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.28/1.04    inference(definition_unfolding,[],[f64,f96])).
% 3.28/1.04  
% 3.28/1.04  fof(f98,plain,(
% 3.28/1.04    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.28/1.04    inference(definition_unfolding,[],[f63,f97])).
% 3.28/1.04  
% 3.28/1.04  fof(f99,plain,(
% 3.28/1.04    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.28/1.04    inference(definition_unfolding,[],[f62,f98])).
% 3.28/1.04  
% 3.28/1.04  fof(f100,plain,(
% 3.28/1.04    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.28/1.04    inference(definition_unfolding,[],[f61,f99])).
% 3.28/1.04  
% 3.28/1.04  fof(f101,plain,(
% 3.28/1.04    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.28/1.04    inference(definition_unfolding,[],[f60,f100])).
% 3.28/1.04  
% 3.28/1.04  fof(f107,plain,(
% 3.28/1.04    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))),
% 3.28/1.04    inference(definition_unfolding,[],[f93,f101])).
% 3.28/1.04  
% 3.28/1.04  fof(f92,plain,(
% 3.28/1.04    v1_funct_2(sK4,k1_tarski(sK2),sK3)),
% 3.28/1.04    inference(cnf_transformation,[],[f49])).
% 3.28/1.04  
% 3.28/1.04  fof(f108,plain,(
% 3.28/1.04    v1_funct_2(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)),
% 3.28/1.04    inference(definition_unfolding,[],[f92,f101])).
% 3.28/1.04  
% 3.28/1.04  fof(f21,axiom,(
% 3.28/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.28/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/1.04  
% 3.28/1.04  fof(f31,plain,(
% 3.28/1.04    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.28/1.04    inference(ennf_transformation,[],[f21])).
% 3.28/1.04  
% 3.28/1.04  fof(f32,plain,(
% 3.28/1.04    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.28/1.04    inference(flattening,[],[f31])).
% 3.28/1.04  
% 3.28/1.04  fof(f47,plain,(
% 3.28/1.04    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.28/1.04    inference(nnf_transformation,[],[f32])).
% 3.28/1.04  
% 3.28/1.04  fof(f84,plain,(
% 3.28/1.04    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.28/1.04    inference(cnf_transformation,[],[f47])).
% 3.28/1.04  
% 3.28/1.04  fof(f94,plain,(
% 3.28/1.04    k1_xboole_0 != sK3),
% 3.28/1.04    inference(cnf_transformation,[],[f49])).
% 3.28/1.04  
% 3.28/1.04  fof(f17,axiom,(
% 3.28/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.28/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/1.04  
% 3.28/1.04  fof(f27,plain,(
% 3.28/1.04    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.28/1.04    inference(ennf_transformation,[],[f17])).
% 3.28/1.04  
% 3.28/1.04  fof(f76,plain,(
% 3.28/1.04    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.28/1.04    inference(cnf_transformation,[],[f27])).
% 3.28/1.04  
% 3.28/1.04  fof(f19,axiom,(
% 3.28/1.04    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) => (r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1))),
% 3.28/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/1.04  
% 3.28/1.04  fof(f29,plain,(
% 3.28/1.04    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1) | ~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)))),
% 3.28/1.04    inference(ennf_transformation,[],[f19])).
% 3.28/1.04  
% 3.28/1.04  fof(f79,plain,(
% 3.28/1.04    ( ! [X2,X0,X1] : (k1_mcart_1(X0) = X1 | ~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))) )),
% 3.28/1.04    inference(cnf_transformation,[],[f29])).
% 3.28/1.04  
% 3.28/1.04  fof(f106,plain,(
% 3.28/1.04    ( ! [X2,X0,X1] : (k1_mcart_1(X0) = X1 | ~r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2))) )),
% 3.28/1.04    inference(definition_unfolding,[],[f79,f101])).
% 3.28/1.04  
% 3.28/1.04  fof(f18,axiom,(
% 3.28/1.04    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 3.28/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/1.04  
% 3.28/1.04  fof(f28,plain,(
% 3.28/1.04    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 3.28/1.04    inference(ennf_transformation,[],[f18])).
% 3.28/1.04  
% 3.28/1.04  fof(f77,plain,(
% 3.28/1.04    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 3.28/1.04    inference(cnf_transformation,[],[f28])).
% 3.28/1.04  
% 3.28/1.04  fof(f22,axiom,(
% 3.28/1.04    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 3.28/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/1.04  
% 3.28/1.04  fof(f33,plain,(
% 3.28/1.04    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.28/1.04    inference(ennf_transformation,[],[f22])).
% 3.28/1.04  
% 3.28/1.04  fof(f34,plain,(
% 3.28/1.04    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.28/1.04    inference(flattening,[],[f33])).
% 3.28/1.04  
% 3.28/1.04  fof(f90,plain,(
% 3.28/1.04    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.28/1.04    inference(cnf_transformation,[],[f34])).
% 3.28/1.04  
% 3.28/1.04  fof(f91,plain,(
% 3.28/1.04    v1_funct_1(sK4)),
% 3.28/1.04    inference(cnf_transformation,[],[f49])).
% 3.28/1.04  
% 3.28/1.04  fof(f95,plain,(
% 3.28/1.04    ~r2_hidden(k1_funct_1(sK4,sK2),sK3)),
% 3.28/1.04    inference(cnf_transformation,[],[f49])).
% 3.28/1.04  
% 3.28/1.04  fof(f16,axiom,(
% 3.28/1.04    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.28/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/1.04  
% 3.28/1.04  fof(f74,plain,(
% 3.28/1.04    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.28/1.04    inference(cnf_transformation,[],[f16])).
% 3.28/1.04  
% 3.28/1.04  fof(f14,axiom,(
% 3.28/1.04    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 3.28/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/1.04  
% 3.28/1.04  fof(f44,plain,(
% 3.28/1.04    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 3.28/1.04    inference(nnf_transformation,[],[f14])).
% 3.28/1.04  
% 3.28/1.04  fof(f71,plain,(
% 3.28/1.04    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 3.28/1.04    inference(cnf_transformation,[],[f44])).
% 3.28/1.04  
% 3.28/1.04  fof(f3,axiom,(
% 3.28/1.04    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 3.28/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/1.04  
% 3.28/1.04  fof(f57,plain,(
% 3.28/1.04    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 3.28/1.04    inference(cnf_transformation,[],[f3])).
% 3.28/1.04  
% 3.28/1.04  fof(f104,plain,(
% 3.28/1.04    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k5_xboole_0(X0,k3_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) != X0) )),
% 3.28/1.04    inference(definition_unfolding,[],[f71,f57,f101])).
% 3.28/1.04  
% 3.28/1.04  fof(f4,axiom,(
% 3.28/1.04    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.28/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/1.04  
% 3.28/1.04  fof(f58,plain,(
% 3.28/1.04    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.28/1.04    inference(cnf_transformation,[],[f4])).
% 3.28/1.04  
% 3.28/1.04  fof(f102,plain,(
% 3.28/1.04    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 3.28/1.04    inference(definition_unfolding,[],[f58,f57])).
% 3.28/1.04  
% 3.28/1.04  cnf(c_6,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f110]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_1671,plain,
% 3.28/1.04      ( r1_tarski(X0,X0) = iProver_top ),
% 3.28/1.04      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_11,plain,
% 3.28/1.04      ( ~ r1_tarski(X0,X1) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 3.28/1.04      inference(cnf_transformation,[],[f111]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_1668,plain,
% 3.28/1.04      ( r1_tarski(X0,X1) != iProver_top
% 3.28/1.04      | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
% 3.28/1.04      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_25,plain,
% 3.28/1.04      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 3.28/1.04      inference(cnf_transformation,[],[f81]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_1658,plain,
% 3.28/1.04      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 3.28/1.04      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_15,plain,
% 3.28/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.28/1.04      | ~ r2_hidden(X2,X0)
% 3.28/1.04      | r2_hidden(X2,X1) ),
% 3.28/1.04      inference(cnf_transformation,[],[f73]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_35,negated_conjecture,
% 3.28/1.04      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) ),
% 3.28/1.04      inference(cnf_transformation,[],[f107]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_476,plain,
% 3.28/1.04      ( ~ r2_hidden(X0,X1)
% 3.28/1.04      | r2_hidden(X0,X2)
% 3.28/1.04      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(X2)
% 3.28/1.04      | sK4 != X1 ),
% 3.28/1.04      inference(resolution_lifted,[status(thm)],[c_15,c_35]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_477,plain,
% 3.28/1.04      ( r2_hidden(X0,X1)
% 3.28/1.04      | ~ r2_hidden(X0,sK4)
% 3.28/1.04      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(X1) ),
% 3.28/1.04      inference(unflattening,[status(thm)],[c_476]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_1656,plain,
% 3.28/1.04      ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(X0)
% 3.28/1.04      | r2_hidden(X1,X0) = iProver_top
% 3.28/1.04      | r2_hidden(X1,sK4) != iProver_top ),
% 3.28/1.04      inference(predicate_to_equality,[status(thm)],[c_477]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_36,negated_conjecture,
% 3.28/1.04      ( v1_funct_2(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) ),
% 3.28/1.04      inference(cnf_transformation,[],[f108]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_31,plain,
% 3.28/1.04      ( ~ v1_funct_2(X0,X1,X2)
% 3.28/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.28/1.04      | k1_relset_1(X1,X2,X0) = X1
% 3.28/1.04      | k1_xboole_0 = X2 ),
% 3.28/1.04      inference(cnf_transformation,[],[f84]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_491,plain,
% 3.28/1.04      ( ~ v1_funct_2(X0,X1,X2)
% 3.28/1.04      | k1_relset_1(X1,X2,X0) = X1
% 3.28/1.04      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 3.28/1.04      | sK4 != X0
% 3.28/1.04      | k1_xboole_0 = X2 ),
% 3.28/1.04      inference(resolution_lifted,[status(thm)],[c_31,c_35]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_492,plain,
% 3.28/1.04      ( ~ v1_funct_2(sK4,X0,X1)
% 3.28/1.04      | k1_relset_1(X0,X1,sK4) = X0
% 3.28/1.04      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.28/1.04      | k1_xboole_0 = X1 ),
% 3.28/1.04      inference(unflattening,[status(thm)],[c_491]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_719,plain,
% 3.28/1.04      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != X0
% 3.28/1.04      | k1_relset_1(X0,X1,sK4) = X0
% 3.28/1.04      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.28/1.04      | sK3 != X1
% 3.28/1.04      | sK4 != sK4
% 3.28/1.04      | k1_xboole_0 = X1 ),
% 3.28/1.04      inference(resolution_lifted,[status(thm)],[c_36,c_492]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_720,plain,
% 3.28/1.04      ( k1_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 3.28/1.04      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))
% 3.28/1.04      | k1_xboole_0 = sK3 ),
% 3.28/1.04      inference(unflattening,[status(thm)],[c_719]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_34,negated_conjecture,
% 3.28/1.04      ( k1_xboole_0 != sK3 ),
% 3.28/1.04      inference(cnf_transformation,[],[f94]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_721,plain,
% 3.28/1.04      ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))
% 3.28/1.04      | k1_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 3.28/1.04      inference(global_propositional_subsumption,[status(thm)],[c_720,c_34]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_722,plain,
% 3.28/1.04      ( k1_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 3.28/1.04      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) ),
% 3.28/1.04      inference(renaming,[status(thm)],[c_721]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_834,plain,
% 3.28/1.04      ( k1_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 3.28/1.04      inference(equality_resolution_simp,[status(thm)],[c_722]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_18,plain,
% 3.28/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.28/1.04      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.28/1.04      inference(cnf_transformation,[],[f76]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_527,plain,
% 3.28/1.04      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.28/1.04      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.28/1.04      | sK4 != X2 ),
% 3.28/1.04      inference(resolution_lifted,[status(thm)],[c_18,c_35]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_528,plain,
% 3.28/1.04      ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
% 3.28/1.04      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 3.28/1.04      inference(unflattening,[status(thm)],[c_527]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_1893,plain,
% 3.28/1.04      ( k1_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4) = k1_relat_1(sK4) ),
% 3.28/1.04      inference(equality_resolution,[status(thm)],[c_528]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_2028,plain,
% 3.28/1.04      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_relat_1(sK4) ),
% 3.28/1.04      inference(light_normalisation,[status(thm)],[c_834,c_1893]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_2301,plain,
% 3.28/1.04      ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3)) != k1_zfmisc_1(X0)
% 3.28/1.04      | r2_hidden(X1,X0) = iProver_top
% 3.28/1.04      | r2_hidden(X1,sK4) != iProver_top ),
% 3.28/1.04      inference(light_normalisation,[status(thm)],[c_1656,c_2028]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_2308,plain,
% 3.28/1.04      ( r2_hidden(X0,k2_zfmisc_1(k1_relat_1(sK4),sK3)) = iProver_top
% 3.28/1.04      | r2_hidden(X0,sK4) != iProver_top ),
% 3.28/1.04      inference(equality_resolution,[status(thm)],[c_2301]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_22,plain,
% 3.28/1.04      ( ~ r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2))
% 3.28/1.04      | k1_mcart_1(X0) = X1 ),
% 3.28/1.04      inference(cnf_transformation,[],[f106]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_1661,plain,
% 3.28/1.04      ( k1_mcart_1(X0) = X1
% 3.28/1.04      | r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)) != iProver_top ),
% 3.28/1.04      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_3536,plain,
% 3.28/1.04      ( k1_mcart_1(X0) = sK2
% 3.28/1.04      | r2_hidden(X0,k2_zfmisc_1(k1_relat_1(sK4),X1)) != iProver_top ),
% 3.28/1.04      inference(superposition,[status(thm)],[c_2028,c_1661]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_3903,plain,
% 3.28/1.04      ( k1_mcart_1(X0) = sK2 | r2_hidden(X0,sK4) != iProver_top ),
% 3.28/1.04      inference(superposition,[status(thm)],[c_2308,c_3536]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_3929,plain,
% 3.28/1.04      ( k1_mcart_1(sK1(sK4)) = sK2 | sK4 = k1_xboole_0 ),
% 3.28/1.04      inference(superposition,[status(thm)],[c_1658,c_3903]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_20,plain,
% 3.28/1.04      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1) ),
% 3.28/1.04      inference(cnf_transformation,[],[f77]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_1663,plain,
% 3.28/1.04      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.28/1.04      | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
% 3.28/1.04      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_3112,plain,
% 3.28/1.04      ( r2_hidden(X0,sK4) != iProver_top
% 3.28/1.04      | r2_hidden(k1_mcart_1(X0),k1_relat_1(sK4)) = iProver_top ),
% 3.28/1.04      inference(superposition,[status(thm)],[c_2308,c_1663]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_4451,plain,
% 3.28/1.04      ( sK4 = k1_xboole_0
% 3.28/1.04      | r2_hidden(sK1(sK4),sK4) != iProver_top
% 3.28/1.04      | r2_hidden(sK2,k1_relat_1(sK4)) = iProver_top ),
% 3.28/1.04      inference(superposition,[status(thm)],[c_3929,c_3112]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_32,plain,
% 3.28/1.04      ( ~ v1_funct_2(X0,X1,X2)
% 3.28/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.28/1.04      | ~ r2_hidden(X3,X1)
% 3.28/1.04      | r2_hidden(k1_funct_1(X0,X3),X2)
% 3.28/1.04      | ~ v1_funct_1(X0)
% 3.28/1.04      | k1_xboole_0 = X2 ),
% 3.28/1.04      inference(cnf_transformation,[],[f90]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_37,negated_conjecture,
% 3.28/1.04      ( v1_funct_1(sK4) ),
% 3.28/1.04      inference(cnf_transformation,[],[f91]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_449,plain,
% 3.28/1.04      ( ~ v1_funct_2(X0,X1,X2)
% 3.28/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.28/1.04      | ~ r2_hidden(X3,X1)
% 3.28/1.04      | r2_hidden(k1_funct_1(X0,X3),X2)
% 3.28/1.04      | sK4 != X0
% 3.28/1.04      | k1_xboole_0 = X2 ),
% 3.28/1.04      inference(resolution_lifted,[status(thm)],[c_32,c_37]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_450,plain,
% 3.28/1.04      ( ~ v1_funct_2(sK4,X0,X1)
% 3.28/1.04      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.28/1.04      | ~ r2_hidden(X2,X0)
% 3.28/1.04      | r2_hidden(k1_funct_1(sK4,X2),X1)
% 3.28/1.04      | k1_xboole_0 = X1 ),
% 3.28/1.04      inference(unflattening,[status(thm)],[c_449]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_601,plain,
% 3.28/1.04      ( ~ v1_funct_2(sK4,X0,X1)
% 3.28/1.04      | ~ r2_hidden(X2,X0)
% 3.28/1.04      | r2_hidden(k1_funct_1(sK4,X2),X1)
% 3.28/1.04      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.28/1.04      | sK4 != sK4
% 3.28/1.04      | k1_xboole_0 = X1 ),
% 3.28/1.04      inference(resolution_lifted,[status(thm)],[c_35,c_450]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_698,plain,
% 3.28/1.04      ( ~ r2_hidden(X0,X1)
% 3.28/1.04      | r2_hidden(k1_funct_1(sK4,X0),X2)
% 3.28/1.04      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != X1
% 3.28/1.04      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 3.28/1.04      | sK3 != X2
% 3.28/1.04      | sK4 != sK4
% 3.28/1.04      | k1_xboole_0 = X2 ),
% 3.28/1.04      inference(resolution_lifted,[status(thm)],[c_36,c_601]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_699,plain,
% 3.28/1.04      ( ~ r2_hidden(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 3.28/1.04      | r2_hidden(k1_funct_1(sK4,X0),sK3)
% 3.28/1.04      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))
% 3.28/1.04      | k1_xboole_0 = sK3 ),
% 3.28/1.04      inference(unflattening,[status(thm)],[c_698]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_703,plain,
% 3.28/1.04      ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))
% 3.28/1.04      | r2_hidden(k1_funct_1(sK4,X0),sK3)
% 3.28/1.04      | ~ r2_hidden(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
% 3.28/1.04      inference(global_propositional_subsumption,[status(thm)],[c_699,c_34]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_704,plain,
% 3.28/1.04      ( ~ r2_hidden(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 3.28/1.04      | r2_hidden(k1_funct_1(sK4,X0),sK3)
% 3.28/1.04      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) ),
% 3.28/1.04      inference(renaming,[status(thm)],[c_703]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_835,plain,
% 3.28/1.04      ( ~ r2_hidden(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 3.28/1.04      | r2_hidden(k1_funct_1(sK4,X0),sK3) ),
% 3.28/1.04      inference(equality_resolution_simp,[status(thm)],[c_704]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_1654,plain,
% 3.28/1.04      ( r2_hidden(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top
% 3.28/1.04      | r2_hidden(k1_funct_1(sK4,X0),sK3) = iProver_top ),
% 3.28/1.04      inference(predicate_to_equality,[status(thm)],[c_835]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_2450,plain,
% 3.28/1.04      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 3.28/1.04      | r2_hidden(k1_funct_1(sK4,X0),sK3) = iProver_top ),
% 3.28/1.04      inference(light_normalisation,[status(thm)],[c_1654,c_2028]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_33,negated_conjecture,
% 3.28/1.04      ( ~ r2_hidden(k1_funct_1(sK4,sK2),sK3) ),
% 3.28/1.04      inference(cnf_transformation,[],[f95]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_1657,plain,
% 3.28/1.04      ( r2_hidden(k1_funct_1(sK4,sK2),sK3) != iProver_top ),
% 3.28/1.04      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_2456,plain,
% 3.28/1.04      ( r2_hidden(sK2,k1_relat_1(sK4)) != iProver_top ),
% 3.28/1.04      inference(superposition,[status(thm)],[c_2450,c_1657]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_4454,plain,
% 3.28/1.04      ( r2_hidden(sK1(sK4),sK4) != iProver_top | sK4 = k1_xboole_0 ),
% 3.28/1.04      inference(global_propositional_subsumption,[status(thm)],[c_4451,c_2456]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_4455,plain,
% 3.28/1.04      ( sK4 = k1_xboole_0 | r2_hidden(sK1(sK4),sK4) != iProver_top ),
% 3.28/1.04      inference(renaming,[status(thm)],[c_4454]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_4460,plain,
% 3.28/1.04      ( sK4 = k1_xboole_0 ),
% 3.28/1.04      inference(superposition,[status(thm)],[c_1658,c_4455]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_7246,plain,
% 3.28/1.04      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_relat_1(k1_xboole_0) ),
% 3.28/1.04      inference(demodulation,[status(thm)],[c_4460,c_2028]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_17,plain,
% 3.28/1.04      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.28/1.04      inference(cnf_transformation,[],[f74]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_7251,plain,
% 3.28/1.04      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_xboole_0 ),
% 3.28/1.04      inference(light_normalisation,[status(thm)],[c_7246,c_17]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_14,plain,
% 3.28/1.04      ( ~ r2_hidden(X0,X1)
% 3.28/1.04      | k5_xboole_0(X1,k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) != X1 ),
% 3.28/1.04      inference(cnf_transformation,[],[f104]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_1665,plain,
% 3.28/1.04      ( k5_xboole_0(X0,k3_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) != X0
% 3.28/1.04      | r2_hidden(X1,X0) != iProver_top ),
% 3.28/1.04      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_7339,plain,
% 3.28/1.04      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) != X0
% 3.28/1.04      | r2_hidden(sK2,X0) != iProver_top ),
% 3.28/1.04      inference(superposition,[status(thm)],[c_7251,c_1665]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_7,plain,
% 3.28/1.04      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 3.28/1.04      inference(cnf_transformation,[],[f102]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_7343,plain,
% 3.28/1.04      ( X0 != X0 | r2_hidden(sK2,X0) != iProver_top ),
% 3.28/1.04      inference(light_normalisation,[status(thm)],[c_7339,c_7]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_7344,plain,
% 3.28/1.04      ( r2_hidden(sK2,X0) != iProver_top ),
% 3.28/1.04      inference(equality_resolution_simp,[status(thm)],[c_7343]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_9066,plain,
% 3.28/1.04      ( r1_tarski(sK2,X0) != iProver_top ),
% 3.28/1.04      inference(superposition,[status(thm)],[c_1668,c_7344]) ).
% 3.28/1.04  
% 3.28/1.04  cnf(c_9197,plain,
% 3.28/1.04      ( $false ),
% 3.28/1.04      inference(superposition,[status(thm)],[c_1671,c_9066]) ).
% 3.28/1.04  
% 3.28/1.04  
% 3.28/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 3.28/1.04  
% 3.28/1.04  ------                               Statistics
% 3.28/1.04  
% 3.28/1.04  ------ General
% 3.28/1.04  
% 3.28/1.04  abstr_ref_over_cycles:                  0
% 3.28/1.04  abstr_ref_under_cycles:                 0
% 3.28/1.04  gc_basic_clause_elim:                   0
% 3.28/1.04  forced_gc_time:                         0
% 3.28/1.04  parsing_time:                           0.013
% 3.28/1.04  unif_index_cands_time:                  0.
% 3.28/1.04  unif_index_add_time:                    0.
% 3.28/1.04  orderings_time:                         0.
% 3.28/1.04  out_proof_time:                         0.01
% 3.28/1.04  total_time:                             0.274
% 3.28/1.04  num_of_symbols:                         54
% 3.28/1.04  num_of_terms:                           10553
% 3.28/1.04  
% 3.28/1.04  ------ Preprocessing
% 3.28/1.04  
% 3.28/1.04  num_of_splits:                          0
% 3.28/1.04  num_of_split_atoms:                     0
% 3.28/1.04  num_of_reused_defs:                     0
% 3.28/1.04  num_eq_ax_congr_red:                    35
% 3.28/1.04  num_of_sem_filtered_clauses:            1
% 3.28/1.04  num_of_subtypes:                        0
% 3.28/1.04  monotx_restored_types:                  0
% 3.28/1.04  sat_num_of_epr_types:                   0
% 3.28/1.04  sat_num_of_non_cyclic_types:            0
% 3.28/1.04  sat_guarded_non_collapsed_types:        0
% 3.28/1.04  num_pure_diseq_elim:                    0
% 3.28/1.04  simp_replaced_by:                       0
% 3.28/1.04  res_preprocessed:                       163
% 3.28/1.04  prep_upred:                             0
% 3.28/1.04  prep_unflattend:                        31
% 3.28/1.04  smt_new_axioms:                         0
% 3.28/1.04  pred_elim_cands:                        2
% 3.28/1.04  pred_elim:                              3
% 3.28/1.04  pred_elim_cl:                           4
% 3.28/1.04  pred_elim_cycles:                       5
% 3.28/1.04  merged_defs:                            16
% 3.28/1.04  merged_defs_ncl:                        0
% 3.28/1.04  bin_hyper_res:                          16
% 3.28/1.04  prep_cycles:                            4
% 3.28/1.04  pred_elim_time:                         0.015
% 3.28/1.04  splitting_time:                         0.
% 3.28/1.04  sem_filter_time:                        0.
% 3.28/1.04  monotx_time:                            0.001
% 3.28/1.04  subtype_inf_time:                       0.
% 3.28/1.04  
% 3.28/1.04  ------ Problem properties
% 3.28/1.04  
% 3.28/1.04  clauses:                                33
% 3.28/1.04  conjectures:                            2
% 3.28/1.04  epr:                                    3
% 3.28/1.04  horn:                                   24
% 3.28/1.04  ground:                                 7
% 3.28/1.04  unary:                                  8
% 3.28/1.04  binary:                                 11
% 3.28/1.04  lits:                                   77
% 3.28/1.04  lits_eq:                                33
% 3.28/1.04  fd_pure:                                0
% 3.28/1.04  fd_pseudo:                              0
% 3.28/1.04  fd_cond:                                5
% 3.28/1.04  fd_pseudo_cond:                         4
% 3.28/1.04  ac_symbols:                             0
% 3.28/1.04  
% 3.28/1.04  ------ Propositional Solver
% 3.28/1.04  
% 3.28/1.04  prop_solver_calls:                      27
% 3.28/1.04  prop_fast_solver_calls:                 1066
% 3.28/1.04  smt_solver_calls:                       0
% 3.28/1.04  smt_fast_solver_calls:                  0
% 3.28/1.04  prop_num_of_clauses:                    3481
% 3.28/1.04  prop_preprocess_simplified:             9953
% 3.28/1.04  prop_fo_subsumed:                       13
% 3.28/1.04  prop_solver_time:                       0.
% 3.28/1.04  smt_solver_time:                        0.
% 3.28/1.04  smt_fast_solver_time:                   0.
% 3.28/1.04  prop_fast_solver_time:                  0.
% 3.28/1.04  prop_unsat_core_time:                   0.
% 3.28/1.04  
% 3.28/1.04  ------ QBF
% 3.28/1.04  
% 3.28/1.04  qbf_q_res:                              0
% 3.28/1.04  qbf_num_tautologies:                    0
% 3.28/1.04  qbf_prep_cycles:                        0
% 3.28/1.04  
% 3.28/1.04  ------ BMC1
% 3.28/1.04  
% 3.28/1.04  bmc1_current_bound:                     -1
% 3.28/1.04  bmc1_last_solved_bound:                 -1
% 3.28/1.04  bmc1_unsat_core_size:                   -1
% 3.28/1.04  bmc1_unsat_core_parents_size:           -1
% 3.28/1.04  bmc1_merge_next_fun:                    0
% 3.28/1.04  bmc1_unsat_core_clauses_time:           0.
% 3.28/1.04  
% 3.28/1.04  ------ Instantiation
% 3.28/1.04  
% 3.28/1.04  inst_num_of_clauses:                    914
% 3.28/1.04  inst_num_in_passive:                    525
% 3.28/1.04  inst_num_in_active:                     270
% 3.28/1.04  inst_num_in_unprocessed:                119
% 3.28/1.04  inst_num_of_loops:                      400
% 3.28/1.04  inst_num_of_learning_restarts:          0
% 3.28/1.04  inst_num_moves_active_passive:          129
% 3.28/1.04  inst_lit_activity:                      0
% 3.28/1.04  inst_lit_activity_moves:                0
% 3.28/1.04  inst_num_tautologies:                   0
% 3.28/1.04  inst_num_prop_implied:                  0
% 3.28/1.04  inst_num_existing_simplified:           0
% 3.28/1.04  inst_num_eq_res_simplified:             0
% 3.28/1.04  inst_num_child_elim:                    0
% 3.28/1.04  inst_num_of_dismatching_blockings:      730
% 3.28/1.04  inst_num_of_non_proper_insts:           622
% 3.28/1.04  inst_num_of_duplicates:                 0
% 3.28/1.04  inst_inst_num_from_inst_to_res:         0
% 3.28/1.04  inst_dismatching_checking_time:         0.
% 3.28/1.04  
% 3.28/1.04  ------ Resolution
% 3.28/1.04  
% 3.28/1.04  res_num_of_clauses:                     0
% 3.28/1.04  res_num_in_passive:                     0
% 3.28/1.04  res_num_in_active:                      0
% 3.28/1.04  res_num_of_loops:                       167
% 3.28/1.04  res_forward_subset_subsumed:            64
% 3.28/1.04  res_backward_subset_subsumed:           0
% 3.28/1.04  res_forward_subsumed:                   0
% 3.28/1.04  res_backward_subsumed:                  0
% 3.28/1.04  res_forward_subsumption_resolution:     0
% 3.28/1.04  res_backward_subsumption_resolution:    0
% 3.28/1.04  res_clause_to_clause_subsumption:       324
% 3.28/1.04  res_orphan_elimination:                 0
% 3.28/1.04  res_tautology_del:                      69
% 3.28/1.04  res_num_eq_res_simplified:              3
% 3.28/1.04  res_num_sel_changes:                    0
% 3.28/1.04  res_moves_from_active_to_pass:          0
% 3.28/1.04  
% 3.28/1.04  ------ Superposition
% 3.28/1.04  
% 3.28/1.04  sup_time_total:                         0.
% 3.28/1.04  sup_time_generating:                    0.
% 3.28/1.04  sup_time_sim_full:                      0.
% 3.28/1.04  sup_time_sim_immed:                     0.
% 3.28/1.04  
% 3.28/1.04  sup_num_of_clauses:                     100
% 3.28/1.04  sup_num_in_active:                      42
% 3.28/1.04  sup_num_in_passive:                     58
% 3.28/1.04  sup_num_of_loops:                       78
% 3.28/1.04  sup_fw_superposition:                   71
% 3.28/1.04  sup_bw_superposition:                   80
% 3.28/1.04  sup_immediate_simplified:               54
% 3.28/1.04  sup_given_eliminated:                   3
% 3.28/1.04  comparisons_done:                       0
% 3.28/1.04  comparisons_avoided:                    20
% 3.28/1.04  
% 3.28/1.04  ------ Simplifications
% 3.28/1.04  
% 3.28/1.04  
% 3.28/1.04  sim_fw_subset_subsumed:                 11
% 3.28/1.04  sim_bw_subset_subsumed:                 13
% 3.28/1.04  sim_fw_subsumed:                        12
% 3.28/1.04  sim_bw_subsumed:                        3
% 3.28/1.04  sim_fw_subsumption_res:                 6
% 3.28/1.04  sim_bw_subsumption_res:                 0
% 3.28/1.04  sim_tautology_del:                      22
% 3.28/1.04  sim_eq_tautology_del:                   7
% 3.28/1.04  sim_eq_res_simp:                        2
% 3.28/1.04  sim_fw_demodulated:                     2
% 3.28/1.04  sim_bw_demodulated:                     37
% 3.28/1.04  sim_light_normalised:                   32
% 3.28/1.04  sim_joinable_taut:                      0
% 3.28/1.04  sim_joinable_simp:                      0
% 3.28/1.04  sim_ac_normalised:                      0
% 3.28/1.04  sim_smt_subsumption:                    0
% 3.28/1.04  
%------------------------------------------------------------------------------
