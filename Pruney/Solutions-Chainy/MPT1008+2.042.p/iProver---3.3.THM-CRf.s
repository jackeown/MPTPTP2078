%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:13 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :  145 (1337 expanded)
%              Number of clauses        :   70 ( 277 expanded)
%              Number of leaves         :   23 ( 351 expanded)
%              Depth                    :   20
%              Number of atoms          :  412 (3331 expanded)
%              Number of equality atoms :  215 (1760 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f16])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X4,X3,X2] :
            ( k3_mcart_1(X2,X3,X4) != sK2(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK2(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK2(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f46])).

fof(f72,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f36,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f37,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f49,plain,
    ( ? [X0,X1,X2] :
        ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( k1_tarski(k1_funct_1(sK5,sK3)) != k2_relset_1(k1_tarski(sK3),sK4,sK5)
      & k1_xboole_0 != sK4
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4)))
      & v1_funct_2(sK5,k1_tarski(sK3),sK4)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( k1_tarski(k1_funct_1(sK5,sK3)) != k2_relset_1(k1_tarski(sK3),sK4,sK5)
    & k1_xboole_0 != sK4
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4)))
    & v1_funct_2(sK5,k1_tarski(sK3),sK4)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f37,f49])).

fof(f83,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4))) ),
    inference(cnf_transformation,[],[f50])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f86,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f53,f54])).

fof(f87,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f52,f86])).

fof(f93,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) ),
    inference(definition_unfolding,[],[f83,f87])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f38])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f55,f87,f87])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f85,plain,(
    k1_tarski(k1_funct_1(sK5,sK3)) != k2_relset_1(k1_tarski(sK3),sK4,sK5) ),
    inference(cnf_transformation,[],[f50])).

fof(f92,plain,(
    k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) ),
    inference(definition_unfolding,[],[f85,f87,f87])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f91,plain,(
    ! [X0,X1] :
      ( k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f64,f87,f87])).

fof(f81,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f50])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f62,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f17,axiom,(
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

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

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
    inference(nnf_transformation,[],[f35])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f82,plain,(
    v1_funct_2(sK5,k1_tarski(sK3),sK4) ),
    inference(cnf_transformation,[],[f50])).

fof(f94,plain,(
    v1_funct_2(sK5,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
    inference(definition_unfolding,[],[f82,f87])).

fof(f84,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f50])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ? [X3] :
              ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ? [X5] :
              ( ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X2)
              & r2_hidden(X5,X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(rectify,[],[f41])).

fof(f44,plain,(
    ! [X2,X1] :
      ( ? [X5] :
          ( ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X2)
          & r2_hidden(X5,X1) )
     => ( ! [X6] : ~ r2_hidden(k4_tarski(sK1(X1,X2),X6),X2)
        & r2_hidden(sK1(X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X3,X2] :
      ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
     => r2_hidden(k4_tarski(X3,sK0(X2,X3)),X2) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( r2_hidden(k4_tarski(X3,sK0(X2,X3)),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ( ! [X6] : ~ r2_hidden(k4_tarski(sK1(X1,X2),X6),X2)
            & r2_hidden(sK1(X1,X2),X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f42,f44,f43])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X3,sK0(X2,X3)),X2)
      | ~ r2_hidden(X3,X1)
      | k1_relset_1(X1,X0,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_20,plain,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1115,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1114,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_13,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_7,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_363,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_13,c_7])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_367,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_363,c_12])).

cnf(c_368,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_367])).

cnf(c_465,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_enumset1(X3,X3,X3,X3) != X1
    | k2_enumset1(X3,X3,X3,X3) = X4
    | k1_relat_1(X0) != X4
    | k1_xboole_0 = X4 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_368])).

cnf(c_466,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2)))
    | k2_enumset1(X1,X1,X1,X1) = k1_relat_1(X0)
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_465])).

cnf(c_1110,plain,
    ( k2_enumset1(X0,X0,X0,X0) = k1_relat_1(X1)
    | k1_xboole_0 = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_466])).

cnf(c_1876,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_relat_1(sK5)
    | k1_relat_1(sK5) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1114,c_1110])).

cnf(c_27,negated_conjecture,
    ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1295,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1308,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))
    | k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_753,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1301,plain,
    ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != X0
    | k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) = k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5)
    | k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) != X0 ),
    inference(instantiation,[status(thm)],[c_753])).

cnf(c_1374,plain,
    ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) = k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5)
    | k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relat_1(sK5)
    | k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) != k2_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1301])).

cnf(c_10,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_344,plain,
    ( ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_31])).

cnf(c_345,plain,
    ( ~ v1_relat_1(sK5)
    | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5)
    | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_344])).

cnf(c_1410,plain,
    ( ~ v1_relat_1(sK5)
    | k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) = k2_relat_1(sK5)
    | k2_enumset1(sK3,sK3,sK3,sK3) != k1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_345])).

cnf(c_2179,plain,
    ( k1_relat_1(sK5) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1876,c_29,c_27,c_1295,c_1308,c_1374,c_1410])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1123,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2190,plain,
    ( sK5 = k1_xboole_0
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2179,c_1123])).

cnf(c_1389,plain,
    ( ~ v1_relat_1(sK5)
    | k1_relat_1(sK5) != k1_xboole_0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_752,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1401,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_752])).

cnf(c_1717,plain,
    ( sK5 != X0
    | sK5 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_753])).

cnf(c_2127,plain,
    ( sK5 != sK5
    | sK5 = k1_xboole_0
    | k1_xboole_0 != sK5 ),
    inference(instantiation,[status(thm)],[c_1717])).

cnf(c_2193,plain,
    ( sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2190,c_29,c_27,c_1295,c_1308,c_1374,c_1389,c_1401,c_1410,c_1876,c_2127])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK5,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_548,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_enumset1(sK3,sK3,sK3,sK3) != X1
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X2
    | sK5 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_30])).

cnf(c_549,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))
    | k1_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_enumset1(sK3,sK3,sK3,sK3)
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_548])).

cnf(c_28,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_551,plain,
    ( k1_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_549,c_29,c_28])).

cnf(c_2202,plain,
    ( k1_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0) = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(demodulation,[status(thm)],[c_2193,c_551])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k4_tarski(X0,sK0(X2,X0)),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | k1_relset_1(X1,X3,X2) != X1 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1120,plain,
    ( k1_relset_1(X0,X1,X2) != X0
    | r2_hidden(X3,X0) != iProver_top
    | r2_hidden(k4_tarski(X3,sK0(X2,X3)),X2) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2713,plain,
    ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK0(k1_xboole_0,X0)),k1_xboole_0) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2202,c_1120])).

cnf(c_4,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1126,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_438,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_11])).

cnf(c_439,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_438])).

cnf(c_1112,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_439])).

cnf(c_2887,plain,
    ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2713,c_1126,c_1112])).

cnf(c_2891,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1115,c_2887])).

cnf(c_1113,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5)
    | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5)
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_345])).

cnf(c_34,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_346,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5)
    | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5)
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_345])).

cnf(c_1296,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1295])).

cnf(c_1334,plain,
    ( k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5)
    | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1113,c_34,c_346,c_1296])).

cnf(c_1335,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5)
    | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5) ),
    inference(renaming,[status(thm)],[c_1334])).

cnf(c_2183,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_xboole_0
    | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5) ),
    inference(demodulation,[status(thm)],[c_2179,c_1335])).

cnf(c_2806,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_xboole_0
    | k2_enumset1(k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0)) = k2_relat_1(k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_2183,c_2193])).

cnf(c_2911,plain,
    ( k2_enumset1(k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3)) = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2891,c_2806])).

cnf(c_1121,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1885,plain,
    ( k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1114,c_1121])).

cnf(c_2069,plain,
    ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relat_1(sK5) ),
    inference(demodulation,[status(thm)],[c_1885,c_27])).

cnf(c_2198,plain,
    ( k2_enumset1(k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3)) != k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_2193,c_2069])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2911,c_2198])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:11:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.15/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.01  
% 2.15/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.15/1.01  
% 2.15/1.01  ------  iProver source info
% 2.15/1.01  
% 2.15/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.15/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.15/1.01  git: non_committed_changes: false
% 2.15/1.01  git: last_make_outside_of_git: false
% 2.15/1.01  
% 2.15/1.01  ------ 
% 2.15/1.01  
% 2.15/1.01  ------ Input Options
% 2.15/1.01  
% 2.15/1.01  --out_options                           all
% 2.15/1.01  --tptp_safe_out                         true
% 2.15/1.01  --problem_path                          ""
% 2.15/1.01  --include_path                          ""
% 2.15/1.01  --clausifier                            res/vclausify_rel
% 2.15/1.01  --clausifier_options                    --mode clausify
% 2.15/1.01  --stdin                                 false
% 2.15/1.01  --stats_out                             all
% 2.15/1.01  
% 2.15/1.01  ------ General Options
% 2.15/1.01  
% 2.15/1.01  --fof                                   false
% 2.15/1.01  --time_out_real                         305.
% 2.15/1.01  --time_out_virtual                      -1.
% 2.15/1.01  --symbol_type_check                     false
% 2.15/1.01  --clausify_out                          false
% 2.15/1.01  --sig_cnt_out                           false
% 2.15/1.01  --trig_cnt_out                          false
% 2.15/1.01  --trig_cnt_out_tolerance                1.
% 2.15/1.01  --trig_cnt_out_sk_spl                   false
% 2.15/1.01  --abstr_cl_out                          false
% 2.15/1.01  
% 2.15/1.01  ------ Global Options
% 2.15/1.01  
% 2.15/1.01  --schedule                              default
% 2.15/1.01  --add_important_lit                     false
% 2.15/1.01  --prop_solver_per_cl                    1000
% 2.15/1.01  --min_unsat_core                        false
% 2.15/1.01  --soft_assumptions                      false
% 2.15/1.01  --soft_lemma_size                       3
% 2.15/1.01  --prop_impl_unit_size                   0
% 2.15/1.01  --prop_impl_unit                        []
% 2.15/1.01  --share_sel_clauses                     true
% 2.15/1.01  --reset_solvers                         false
% 2.15/1.01  --bc_imp_inh                            [conj_cone]
% 2.15/1.01  --conj_cone_tolerance                   3.
% 2.15/1.01  --extra_neg_conj                        none
% 2.15/1.01  --large_theory_mode                     true
% 2.15/1.01  --prolific_symb_bound                   200
% 2.15/1.01  --lt_threshold                          2000
% 2.15/1.01  --clause_weak_htbl                      true
% 2.15/1.01  --gc_record_bc_elim                     false
% 2.15/1.01  
% 2.15/1.01  ------ Preprocessing Options
% 2.15/1.01  
% 2.15/1.01  --preprocessing_flag                    true
% 2.15/1.01  --time_out_prep_mult                    0.1
% 2.15/1.01  --splitting_mode                        input
% 2.15/1.01  --splitting_grd                         true
% 2.15/1.01  --splitting_cvd                         false
% 2.15/1.01  --splitting_cvd_svl                     false
% 2.15/1.01  --splitting_nvd                         32
% 2.15/1.01  --sub_typing                            true
% 2.15/1.01  --prep_gs_sim                           true
% 2.15/1.01  --prep_unflatten                        true
% 2.15/1.01  --prep_res_sim                          true
% 2.15/1.01  --prep_upred                            true
% 2.15/1.01  --prep_sem_filter                       exhaustive
% 2.15/1.01  --prep_sem_filter_out                   false
% 2.15/1.01  --pred_elim                             true
% 2.15/1.01  --res_sim_input                         true
% 2.15/1.01  --eq_ax_congr_red                       true
% 2.15/1.01  --pure_diseq_elim                       true
% 2.15/1.01  --brand_transform                       false
% 2.15/1.01  --non_eq_to_eq                          false
% 2.15/1.01  --prep_def_merge                        true
% 2.15/1.01  --prep_def_merge_prop_impl              false
% 2.15/1.01  --prep_def_merge_mbd                    true
% 2.15/1.01  --prep_def_merge_tr_red                 false
% 2.15/1.01  --prep_def_merge_tr_cl                  false
% 2.15/1.01  --smt_preprocessing                     true
% 2.15/1.01  --smt_ac_axioms                         fast
% 2.15/1.01  --preprocessed_out                      false
% 2.15/1.01  --preprocessed_stats                    false
% 2.15/1.01  
% 2.15/1.01  ------ Abstraction refinement Options
% 2.15/1.01  
% 2.15/1.01  --abstr_ref                             []
% 2.15/1.01  --abstr_ref_prep                        false
% 2.15/1.01  --abstr_ref_until_sat                   false
% 2.15/1.01  --abstr_ref_sig_restrict                funpre
% 2.15/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.15/1.01  --abstr_ref_under                       []
% 2.15/1.01  
% 2.15/1.01  ------ SAT Options
% 2.15/1.01  
% 2.15/1.01  --sat_mode                              false
% 2.15/1.01  --sat_fm_restart_options                ""
% 2.15/1.01  --sat_gr_def                            false
% 2.15/1.01  --sat_epr_types                         true
% 2.15/1.01  --sat_non_cyclic_types                  false
% 2.15/1.01  --sat_finite_models                     false
% 2.15/1.01  --sat_fm_lemmas                         false
% 2.15/1.01  --sat_fm_prep                           false
% 2.15/1.01  --sat_fm_uc_incr                        true
% 2.15/1.01  --sat_out_model                         small
% 2.15/1.01  --sat_out_clauses                       false
% 2.15/1.01  
% 2.15/1.01  ------ QBF Options
% 2.15/1.01  
% 2.15/1.01  --qbf_mode                              false
% 2.15/1.01  --qbf_elim_univ                         false
% 2.15/1.01  --qbf_dom_inst                          none
% 2.15/1.01  --qbf_dom_pre_inst                      false
% 2.15/1.01  --qbf_sk_in                             false
% 2.15/1.01  --qbf_pred_elim                         true
% 2.15/1.01  --qbf_split                             512
% 2.15/1.01  
% 2.15/1.01  ------ BMC1 Options
% 2.15/1.01  
% 2.15/1.01  --bmc1_incremental                      false
% 2.15/1.01  --bmc1_axioms                           reachable_all
% 2.15/1.01  --bmc1_min_bound                        0
% 2.15/1.01  --bmc1_max_bound                        -1
% 2.15/1.01  --bmc1_max_bound_default                -1
% 2.15/1.01  --bmc1_symbol_reachability              true
% 2.15/1.01  --bmc1_property_lemmas                  false
% 2.15/1.01  --bmc1_k_induction                      false
% 2.15/1.01  --bmc1_non_equiv_states                 false
% 2.15/1.01  --bmc1_deadlock                         false
% 2.15/1.01  --bmc1_ucm                              false
% 2.15/1.01  --bmc1_add_unsat_core                   none
% 2.15/1.01  --bmc1_unsat_core_children              false
% 2.15/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.15/1.01  --bmc1_out_stat                         full
% 2.15/1.01  --bmc1_ground_init                      false
% 2.15/1.01  --bmc1_pre_inst_next_state              false
% 2.15/1.01  --bmc1_pre_inst_state                   false
% 2.15/1.01  --bmc1_pre_inst_reach_state             false
% 2.15/1.01  --bmc1_out_unsat_core                   false
% 2.15/1.01  --bmc1_aig_witness_out                  false
% 2.15/1.01  --bmc1_verbose                          false
% 2.15/1.01  --bmc1_dump_clauses_tptp                false
% 2.15/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.15/1.01  --bmc1_dump_file                        -
% 2.15/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.15/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.15/1.01  --bmc1_ucm_extend_mode                  1
% 2.15/1.01  --bmc1_ucm_init_mode                    2
% 2.15/1.01  --bmc1_ucm_cone_mode                    none
% 2.15/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.15/1.01  --bmc1_ucm_relax_model                  4
% 2.15/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.15/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.15/1.01  --bmc1_ucm_layered_model                none
% 2.15/1.01  --bmc1_ucm_max_lemma_size               10
% 2.15/1.01  
% 2.15/1.01  ------ AIG Options
% 2.15/1.01  
% 2.15/1.01  --aig_mode                              false
% 2.15/1.01  
% 2.15/1.01  ------ Instantiation Options
% 2.15/1.01  
% 2.15/1.01  --instantiation_flag                    true
% 2.15/1.01  --inst_sos_flag                         false
% 2.15/1.01  --inst_sos_phase                        true
% 2.15/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.15/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.15/1.01  --inst_lit_sel_side                     num_symb
% 2.15/1.01  --inst_solver_per_active                1400
% 2.15/1.01  --inst_solver_calls_frac                1.
% 2.15/1.01  --inst_passive_queue_type               priority_queues
% 2.15/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.15/1.01  --inst_passive_queues_freq              [25;2]
% 2.15/1.01  --inst_dismatching                      true
% 2.15/1.01  --inst_eager_unprocessed_to_passive     true
% 2.15/1.01  --inst_prop_sim_given                   true
% 2.15/1.01  --inst_prop_sim_new                     false
% 2.15/1.01  --inst_subs_new                         false
% 2.15/1.01  --inst_eq_res_simp                      false
% 2.15/1.01  --inst_subs_given                       false
% 2.15/1.01  --inst_orphan_elimination               true
% 2.15/1.01  --inst_learning_loop_flag               true
% 2.15/1.01  --inst_learning_start                   3000
% 2.15/1.01  --inst_learning_factor                  2
% 2.15/1.01  --inst_start_prop_sim_after_learn       3
% 2.15/1.01  --inst_sel_renew                        solver
% 2.15/1.01  --inst_lit_activity_flag                true
% 2.15/1.01  --inst_restr_to_given                   false
% 2.15/1.01  --inst_activity_threshold               500
% 2.15/1.01  --inst_out_proof                        true
% 2.15/1.01  
% 2.15/1.01  ------ Resolution Options
% 2.15/1.01  
% 2.15/1.01  --resolution_flag                       true
% 2.15/1.01  --res_lit_sel                           adaptive
% 2.15/1.01  --res_lit_sel_side                      none
% 2.15/1.01  --res_ordering                          kbo
% 2.15/1.01  --res_to_prop_solver                    active
% 2.15/1.01  --res_prop_simpl_new                    false
% 2.15/1.01  --res_prop_simpl_given                  true
% 2.15/1.01  --res_passive_queue_type                priority_queues
% 2.15/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.15/1.01  --res_passive_queues_freq               [15;5]
% 2.15/1.01  --res_forward_subs                      full
% 2.15/1.01  --res_backward_subs                     full
% 2.15/1.01  --res_forward_subs_resolution           true
% 2.15/1.01  --res_backward_subs_resolution          true
% 2.15/1.01  --res_orphan_elimination                true
% 2.15/1.01  --res_time_limit                        2.
% 2.15/1.01  --res_out_proof                         true
% 2.15/1.01  
% 2.15/1.01  ------ Superposition Options
% 2.15/1.01  
% 2.15/1.01  --superposition_flag                    true
% 2.15/1.01  --sup_passive_queue_type                priority_queues
% 2.15/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.15/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.15/1.01  --demod_completeness_check              fast
% 2.15/1.01  --demod_use_ground                      true
% 2.15/1.01  --sup_to_prop_solver                    passive
% 2.15/1.01  --sup_prop_simpl_new                    true
% 2.15/1.01  --sup_prop_simpl_given                  true
% 2.15/1.01  --sup_fun_splitting                     false
% 2.15/1.01  --sup_smt_interval                      50000
% 2.15/1.01  
% 2.15/1.01  ------ Superposition Simplification Setup
% 2.15/1.01  
% 2.15/1.01  --sup_indices_passive                   []
% 2.15/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.15/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.15/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.15/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.15/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.15/1.01  --sup_full_bw                           [BwDemod]
% 2.15/1.01  --sup_immed_triv                        [TrivRules]
% 2.15/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.15/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.15/1.01  --sup_immed_bw_main                     []
% 2.15/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.15/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.15/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.15/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.15/1.01  
% 2.15/1.01  ------ Combination Options
% 2.15/1.01  
% 2.15/1.01  --comb_res_mult                         3
% 2.15/1.01  --comb_sup_mult                         2
% 2.15/1.01  --comb_inst_mult                        10
% 2.15/1.01  
% 2.15/1.01  ------ Debug Options
% 2.15/1.01  
% 2.15/1.01  --dbg_backtrace                         false
% 2.15/1.01  --dbg_dump_prop_clauses                 false
% 2.15/1.01  --dbg_dump_prop_clauses_file            -
% 2.15/1.01  --dbg_out_stat                          false
% 2.15/1.01  ------ Parsing...
% 2.15/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.15/1.01  
% 2.15/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.15/1.01  
% 2.15/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.15/1.01  
% 2.15/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.15/1.01  ------ Proving...
% 2.15/1.01  ------ Problem Properties 
% 2.15/1.01  
% 2.15/1.01  
% 2.15/1.01  clauses                                 23
% 2.15/1.01  conjectures                             3
% 2.15/1.01  EPR                                     2
% 2.15/1.01  Horn                                    19
% 2.15/1.01  unary                                   7
% 2.15/1.01  binary                                  4
% 2.15/1.01  lits                                    53
% 2.15/1.01  lits eq                                 25
% 2.15/1.01  fd_pure                                 0
% 2.15/1.01  fd_pseudo                               0
% 2.15/1.01  fd_cond                                 5
% 2.15/1.01  fd_pseudo_cond                          0
% 2.15/1.01  AC symbols                              0
% 2.15/1.01  
% 2.15/1.01  ------ Schedule dynamic 5 is on 
% 2.15/1.01  
% 2.15/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.15/1.01  
% 2.15/1.01  
% 2.15/1.01  ------ 
% 2.15/1.01  Current options:
% 2.15/1.01  ------ 
% 2.15/1.01  
% 2.15/1.01  ------ Input Options
% 2.15/1.01  
% 2.15/1.01  --out_options                           all
% 2.15/1.01  --tptp_safe_out                         true
% 2.15/1.01  --problem_path                          ""
% 2.15/1.01  --include_path                          ""
% 2.15/1.01  --clausifier                            res/vclausify_rel
% 2.15/1.01  --clausifier_options                    --mode clausify
% 2.15/1.01  --stdin                                 false
% 2.15/1.01  --stats_out                             all
% 2.15/1.01  
% 2.15/1.01  ------ General Options
% 2.15/1.01  
% 2.15/1.01  --fof                                   false
% 2.15/1.01  --time_out_real                         305.
% 2.15/1.01  --time_out_virtual                      -1.
% 2.15/1.01  --symbol_type_check                     false
% 2.15/1.01  --clausify_out                          false
% 2.15/1.01  --sig_cnt_out                           false
% 2.15/1.01  --trig_cnt_out                          false
% 2.15/1.01  --trig_cnt_out_tolerance                1.
% 2.15/1.01  --trig_cnt_out_sk_spl                   false
% 2.15/1.01  --abstr_cl_out                          false
% 2.15/1.01  
% 2.15/1.01  ------ Global Options
% 2.15/1.01  
% 2.15/1.01  --schedule                              default
% 2.15/1.01  --add_important_lit                     false
% 2.15/1.01  --prop_solver_per_cl                    1000
% 2.15/1.01  --min_unsat_core                        false
% 2.15/1.01  --soft_assumptions                      false
% 2.15/1.01  --soft_lemma_size                       3
% 2.15/1.01  --prop_impl_unit_size                   0
% 2.15/1.01  --prop_impl_unit                        []
% 2.15/1.01  --share_sel_clauses                     true
% 2.15/1.01  --reset_solvers                         false
% 2.15/1.01  --bc_imp_inh                            [conj_cone]
% 2.15/1.01  --conj_cone_tolerance                   3.
% 2.15/1.01  --extra_neg_conj                        none
% 2.15/1.01  --large_theory_mode                     true
% 2.15/1.01  --prolific_symb_bound                   200
% 2.15/1.01  --lt_threshold                          2000
% 2.15/1.01  --clause_weak_htbl                      true
% 2.15/1.01  --gc_record_bc_elim                     false
% 2.15/1.01  
% 2.15/1.01  ------ Preprocessing Options
% 2.15/1.01  
% 2.15/1.01  --preprocessing_flag                    true
% 2.15/1.01  --time_out_prep_mult                    0.1
% 2.15/1.01  --splitting_mode                        input
% 2.15/1.01  --splitting_grd                         true
% 2.15/1.01  --splitting_cvd                         false
% 2.15/1.01  --splitting_cvd_svl                     false
% 2.15/1.01  --splitting_nvd                         32
% 2.15/1.01  --sub_typing                            true
% 2.15/1.01  --prep_gs_sim                           true
% 2.15/1.01  --prep_unflatten                        true
% 2.15/1.01  --prep_res_sim                          true
% 2.15/1.01  --prep_upred                            true
% 2.15/1.01  --prep_sem_filter                       exhaustive
% 2.15/1.01  --prep_sem_filter_out                   false
% 2.15/1.01  --pred_elim                             true
% 2.15/1.01  --res_sim_input                         true
% 2.15/1.01  --eq_ax_congr_red                       true
% 2.15/1.01  --pure_diseq_elim                       true
% 2.15/1.01  --brand_transform                       false
% 2.15/1.01  --non_eq_to_eq                          false
% 2.15/1.01  --prep_def_merge                        true
% 2.15/1.01  --prep_def_merge_prop_impl              false
% 2.15/1.01  --prep_def_merge_mbd                    true
% 2.15/1.01  --prep_def_merge_tr_red                 false
% 2.15/1.01  --prep_def_merge_tr_cl                  false
% 2.15/1.01  --smt_preprocessing                     true
% 2.15/1.01  --smt_ac_axioms                         fast
% 2.15/1.01  --preprocessed_out                      false
% 2.15/1.01  --preprocessed_stats                    false
% 2.15/1.01  
% 2.15/1.01  ------ Abstraction refinement Options
% 2.15/1.01  
% 2.15/1.01  --abstr_ref                             []
% 2.15/1.01  --abstr_ref_prep                        false
% 2.15/1.01  --abstr_ref_until_sat                   false
% 2.15/1.01  --abstr_ref_sig_restrict                funpre
% 2.15/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.15/1.01  --abstr_ref_under                       []
% 2.15/1.01  
% 2.15/1.01  ------ SAT Options
% 2.15/1.01  
% 2.15/1.01  --sat_mode                              false
% 2.15/1.01  --sat_fm_restart_options                ""
% 2.15/1.01  --sat_gr_def                            false
% 2.15/1.01  --sat_epr_types                         true
% 2.15/1.01  --sat_non_cyclic_types                  false
% 2.15/1.01  --sat_finite_models                     false
% 2.15/1.01  --sat_fm_lemmas                         false
% 2.15/1.01  --sat_fm_prep                           false
% 2.15/1.01  --sat_fm_uc_incr                        true
% 2.15/1.01  --sat_out_model                         small
% 2.15/1.01  --sat_out_clauses                       false
% 2.15/1.01  
% 2.15/1.01  ------ QBF Options
% 2.15/1.01  
% 2.15/1.01  --qbf_mode                              false
% 2.15/1.01  --qbf_elim_univ                         false
% 2.15/1.01  --qbf_dom_inst                          none
% 2.15/1.01  --qbf_dom_pre_inst                      false
% 2.15/1.01  --qbf_sk_in                             false
% 2.15/1.01  --qbf_pred_elim                         true
% 2.15/1.01  --qbf_split                             512
% 2.15/1.01  
% 2.15/1.01  ------ BMC1 Options
% 2.15/1.01  
% 2.15/1.01  --bmc1_incremental                      false
% 2.15/1.01  --bmc1_axioms                           reachable_all
% 2.15/1.01  --bmc1_min_bound                        0
% 2.15/1.01  --bmc1_max_bound                        -1
% 2.15/1.01  --bmc1_max_bound_default                -1
% 2.15/1.01  --bmc1_symbol_reachability              true
% 2.15/1.01  --bmc1_property_lemmas                  false
% 2.15/1.01  --bmc1_k_induction                      false
% 2.15/1.01  --bmc1_non_equiv_states                 false
% 2.15/1.01  --bmc1_deadlock                         false
% 2.15/1.01  --bmc1_ucm                              false
% 2.15/1.01  --bmc1_add_unsat_core                   none
% 2.15/1.01  --bmc1_unsat_core_children              false
% 2.15/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.15/1.01  --bmc1_out_stat                         full
% 2.15/1.01  --bmc1_ground_init                      false
% 2.15/1.01  --bmc1_pre_inst_next_state              false
% 2.15/1.01  --bmc1_pre_inst_state                   false
% 2.15/1.01  --bmc1_pre_inst_reach_state             false
% 2.15/1.01  --bmc1_out_unsat_core                   false
% 2.15/1.01  --bmc1_aig_witness_out                  false
% 2.15/1.01  --bmc1_verbose                          false
% 2.15/1.01  --bmc1_dump_clauses_tptp                false
% 2.15/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.15/1.01  --bmc1_dump_file                        -
% 2.15/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.15/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.15/1.01  --bmc1_ucm_extend_mode                  1
% 2.15/1.01  --bmc1_ucm_init_mode                    2
% 2.15/1.01  --bmc1_ucm_cone_mode                    none
% 2.15/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.15/1.01  --bmc1_ucm_relax_model                  4
% 2.15/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.15/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.15/1.01  --bmc1_ucm_layered_model                none
% 2.15/1.01  --bmc1_ucm_max_lemma_size               10
% 2.15/1.01  
% 2.15/1.01  ------ AIG Options
% 2.15/1.01  
% 2.15/1.01  --aig_mode                              false
% 2.15/1.01  
% 2.15/1.01  ------ Instantiation Options
% 2.15/1.01  
% 2.15/1.01  --instantiation_flag                    true
% 2.15/1.01  --inst_sos_flag                         false
% 2.15/1.01  --inst_sos_phase                        true
% 2.15/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.15/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.15/1.01  --inst_lit_sel_side                     none
% 2.15/1.01  --inst_solver_per_active                1400
% 2.15/1.01  --inst_solver_calls_frac                1.
% 2.15/1.01  --inst_passive_queue_type               priority_queues
% 2.15/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.15/1.01  --inst_passive_queues_freq              [25;2]
% 2.15/1.01  --inst_dismatching                      true
% 2.15/1.01  --inst_eager_unprocessed_to_passive     true
% 2.15/1.01  --inst_prop_sim_given                   true
% 2.15/1.01  --inst_prop_sim_new                     false
% 2.15/1.01  --inst_subs_new                         false
% 2.15/1.01  --inst_eq_res_simp                      false
% 2.15/1.01  --inst_subs_given                       false
% 2.15/1.01  --inst_orphan_elimination               true
% 2.15/1.01  --inst_learning_loop_flag               true
% 2.15/1.01  --inst_learning_start                   3000
% 2.15/1.01  --inst_learning_factor                  2
% 2.15/1.01  --inst_start_prop_sim_after_learn       3
% 2.15/1.01  --inst_sel_renew                        solver
% 2.15/1.01  --inst_lit_activity_flag                true
% 2.15/1.01  --inst_restr_to_given                   false
% 2.15/1.01  --inst_activity_threshold               500
% 2.15/1.01  --inst_out_proof                        true
% 2.15/1.01  
% 2.15/1.01  ------ Resolution Options
% 2.15/1.01  
% 2.15/1.01  --resolution_flag                       false
% 2.15/1.01  --res_lit_sel                           adaptive
% 2.15/1.01  --res_lit_sel_side                      none
% 2.15/1.01  --res_ordering                          kbo
% 2.15/1.01  --res_to_prop_solver                    active
% 2.15/1.01  --res_prop_simpl_new                    false
% 2.15/1.01  --res_prop_simpl_given                  true
% 2.15/1.01  --res_passive_queue_type                priority_queues
% 2.15/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.15/1.01  --res_passive_queues_freq               [15;5]
% 2.15/1.01  --res_forward_subs                      full
% 2.15/1.01  --res_backward_subs                     full
% 2.15/1.01  --res_forward_subs_resolution           true
% 2.15/1.01  --res_backward_subs_resolution          true
% 2.15/1.01  --res_orphan_elimination                true
% 2.15/1.01  --res_time_limit                        2.
% 2.15/1.01  --res_out_proof                         true
% 2.15/1.01  
% 2.15/1.01  ------ Superposition Options
% 2.15/1.01  
% 2.15/1.01  --superposition_flag                    true
% 2.15/1.01  --sup_passive_queue_type                priority_queues
% 2.15/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.15/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.15/1.01  --demod_completeness_check              fast
% 2.15/1.01  --demod_use_ground                      true
% 2.15/1.01  --sup_to_prop_solver                    passive
% 2.15/1.01  --sup_prop_simpl_new                    true
% 2.15/1.01  --sup_prop_simpl_given                  true
% 2.15/1.01  --sup_fun_splitting                     false
% 2.15/1.01  --sup_smt_interval                      50000
% 2.15/1.01  
% 2.15/1.01  ------ Superposition Simplification Setup
% 2.15/1.01  
% 2.15/1.01  --sup_indices_passive                   []
% 2.15/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.15/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.15/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.15/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.15/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.15/1.01  --sup_full_bw                           [BwDemod]
% 2.15/1.01  --sup_immed_triv                        [TrivRules]
% 2.15/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.15/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.15/1.01  --sup_immed_bw_main                     []
% 2.15/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.15/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.15/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.15/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.15/1.01  
% 2.15/1.01  ------ Combination Options
% 2.15/1.01  
% 2.15/1.01  --comb_res_mult                         3
% 2.15/1.01  --comb_sup_mult                         2
% 2.15/1.01  --comb_inst_mult                        10
% 2.15/1.01  
% 2.15/1.01  ------ Debug Options
% 2.15/1.01  
% 2.15/1.01  --dbg_backtrace                         false
% 2.15/1.01  --dbg_dump_prop_clauses                 false
% 2.15/1.01  --dbg_dump_prop_clauses_file            -
% 2.15/1.01  --dbg_out_stat                          false
% 2.15/1.01  
% 2.15/1.01  
% 2.15/1.01  
% 2.15/1.01  
% 2.15/1.01  ------ Proving...
% 2.15/1.01  
% 2.15/1.01  
% 2.15/1.01  % SZS status Theorem for theBenchmark.p
% 2.15/1.01  
% 2.15/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.15/1.01  
% 2.15/1.01  fof(f16,axiom,(
% 2.15/1.01    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 2.15/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.15/1.01  
% 2.15/1.01  fof(f33,plain,(
% 2.15/1.01    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 2.15/1.01    inference(ennf_transformation,[],[f16])).
% 2.15/1.01  
% 2.15/1.01  fof(f46,plain,(
% 2.15/1.01    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK2(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK2(X0),X0)))),
% 2.15/1.01    introduced(choice_axiom,[])).
% 2.15/1.01  
% 2.15/1.01  fof(f47,plain,(
% 2.15/1.01    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK2(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK2(X0),X0)) | k1_xboole_0 = X0)),
% 2.15/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f46])).
% 2.15/1.01  
% 2.15/1.01  fof(f72,plain,(
% 2.15/1.01    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 2.15/1.01    inference(cnf_transformation,[],[f47])).
% 2.15/1.01  
% 2.15/1.01  fof(f18,conjecture,(
% 2.15/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 2.15/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.15/1.01  
% 2.15/1.01  fof(f19,negated_conjecture,(
% 2.15/1.01    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 2.15/1.01    inference(negated_conjecture,[],[f18])).
% 2.15/1.01  
% 2.15/1.01  fof(f36,plain,(
% 2.15/1.01    ? [X0,X1,X2] : ((k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 2.15/1.01    inference(ennf_transformation,[],[f19])).
% 2.15/1.01  
% 2.15/1.01  fof(f37,plain,(
% 2.15/1.01    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 2.15/1.01    inference(flattening,[],[f36])).
% 2.15/1.01  
% 2.15/1.01  fof(f49,plain,(
% 2.15/1.01    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_tarski(k1_funct_1(sK5,sK3)) != k2_relset_1(k1_tarski(sK3),sK4,sK5) & k1_xboole_0 != sK4 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4))) & v1_funct_2(sK5,k1_tarski(sK3),sK4) & v1_funct_1(sK5))),
% 2.15/1.01    introduced(choice_axiom,[])).
% 2.15/1.01  
% 2.15/1.01  fof(f50,plain,(
% 2.15/1.01    k1_tarski(k1_funct_1(sK5,sK3)) != k2_relset_1(k1_tarski(sK3),sK4,sK5) & k1_xboole_0 != sK4 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4))) & v1_funct_2(sK5,k1_tarski(sK3),sK4) & v1_funct_1(sK5)),
% 2.15/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f37,f49])).
% 2.15/1.01  
% 2.15/1.01  fof(f83,plain,(
% 2.15/1.01    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4)))),
% 2.15/1.01    inference(cnf_transformation,[],[f50])).
% 2.15/1.01  
% 2.15/1.01  fof(f2,axiom,(
% 2.15/1.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.15/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.15/1.01  
% 2.15/1.01  fof(f52,plain,(
% 2.15/1.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.15/1.01    inference(cnf_transformation,[],[f2])).
% 2.15/1.01  
% 2.15/1.01  fof(f3,axiom,(
% 2.15/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.15/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.15/1.01  
% 2.15/1.01  fof(f53,plain,(
% 2.15/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.15/1.01    inference(cnf_transformation,[],[f3])).
% 2.15/1.01  
% 2.15/1.01  fof(f4,axiom,(
% 2.15/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.15/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.15/1.01  
% 2.15/1.01  fof(f54,plain,(
% 2.15/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.15/1.01    inference(cnf_transformation,[],[f4])).
% 2.15/1.01  
% 2.15/1.01  fof(f86,plain,(
% 2.15/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.15/1.01    inference(definition_unfolding,[],[f53,f54])).
% 2.15/1.01  
% 2.15/1.01  fof(f87,plain,(
% 2.15/1.01    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.15/1.01    inference(definition_unfolding,[],[f52,f86])).
% 2.15/1.01  
% 2.15/1.01  fof(f93,plain,(
% 2.15/1.01    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))),
% 2.15/1.01    inference(definition_unfolding,[],[f83,f87])).
% 2.15/1.01  
% 2.15/1.01  fof(f5,axiom,(
% 2.15/1.01    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.15/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.15/1.01  
% 2.15/1.01  fof(f38,plain,(
% 2.15/1.01    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.15/1.01    inference(nnf_transformation,[],[f5])).
% 2.15/1.01  
% 2.15/1.01  fof(f39,plain,(
% 2.15/1.01    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.15/1.01    inference(flattening,[],[f38])).
% 2.15/1.01  
% 2.15/1.01  fof(f55,plain,(
% 2.15/1.01    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 2.15/1.01    inference(cnf_transformation,[],[f39])).
% 2.15/1.01  
% 2.15/1.01  fof(f90,plain,(
% 2.15/1.01    ( ! [X0,X1] : (k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))) )),
% 2.15/1.01    inference(definition_unfolding,[],[f55,f87,f87])).
% 2.15/1.01  
% 2.15/1.01  fof(f13,axiom,(
% 2.15/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.15/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.15/1.01  
% 2.15/1.01  fof(f20,plain,(
% 2.15/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.15/1.01    inference(pure_predicate_removal,[],[f13])).
% 2.15/1.01  
% 2.15/1.01  fof(f30,plain,(
% 2.15/1.01    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.15/1.01    inference(ennf_transformation,[],[f20])).
% 2.15/1.01  
% 2.15/1.01  fof(f67,plain,(
% 2.15/1.01    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.15/1.01    inference(cnf_transformation,[],[f30])).
% 2.15/1.01  
% 2.15/1.01  fof(f8,axiom,(
% 2.15/1.01    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.15/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.15/1.01  
% 2.15/1.01  fof(f23,plain,(
% 2.15/1.01    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.15/1.01    inference(ennf_transformation,[],[f8])).
% 2.15/1.01  
% 2.15/1.01  fof(f40,plain,(
% 2.15/1.01    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.15/1.01    inference(nnf_transformation,[],[f23])).
% 2.15/1.01  
% 2.15/1.01  fof(f60,plain,(
% 2.15/1.01    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.15/1.01    inference(cnf_transformation,[],[f40])).
% 2.15/1.01  
% 2.15/1.01  fof(f12,axiom,(
% 2.15/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.15/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.15/1.01  
% 2.15/1.01  fof(f29,plain,(
% 2.15/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.15/1.01    inference(ennf_transformation,[],[f12])).
% 2.15/1.01  
% 2.15/1.01  fof(f66,plain,(
% 2.15/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.15/1.01    inference(cnf_transformation,[],[f29])).
% 2.15/1.01  
% 2.15/1.01  fof(f85,plain,(
% 2.15/1.01    k1_tarski(k1_funct_1(sK5,sK3)) != k2_relset_1(k1_tarski(sK3),sK4,sK5)),
% 2.15/1.01    inference(cnf_transformation,[],[f50])).
% 2.15/1.01  
% 2.15/1.01  fof(f92,plain,(
% 2.15/1.01    k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5)),
% 2.15/1.01    inference(definition_unfolding,[],[f85,f87,f87])).
% 2.15/1.01  
% 2.15/1.01  fof(f14,axiom,(
% 2.15/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.15/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.15/1.01  
% 2.15/1.01  fof(f31,plain,(
% 2.15/1.01    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.15/1.01    inference(ennf_transformation,[],[f14])).
% 2.15/1.01  
% 2.15/1.01  fof(f68,plain,(
% 2.15/1.01    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.15/1.01    inference(cnf_transformation,[],[f31])).
% 2.15/1.01  
% 2.15/1.01  fof(f10,axiom,(
% 2.15/1.01    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 2.15/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.15/1.01  
% 2.15/1.01  fof(f26,plain,(
% 2.15/1.01    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.15/1.01    inference(ennf_transformation,[],[f10])).
% 2.15/1.01  
% 2.15/1.01  fof(f27,plain,(
% 2.15/1.01    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.15/1.01    inference(flattening,[],[f26])).
% 2.15/1.01  
% 2.15/1.01  fof(f64,plain,(
% 2.15/1.01    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.15/1.01    inference(cnf_transformation,[],[f27])).
% 2.15/1.01  
% 2.15/1.01  fof(f91,plain,(
% 2.15/1.01    ( ! [X0,X1] : (k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1) | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.15/1.01    inference(definition_unfolding,[],[f64,f87,f87])).
% 2.15/1.01  
% 2.15/1.01  fof(f81,plain,(
% 2.15/1.01    v1_funct_1(sK5)),
% 2.15/1.01    inference(cnf_transformation,[],[f50])).
% 2.15/1.01  
% 2.15/1.01  fof(f9,axiom,(
% 2.15/1.01    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 2.15/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.15/1.01  
% 2.15/1.01  fof(f24,plain,(
% 2.15/1.01    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.15/1.01    inference(ennf_transformation,[],[f9])).
% 2.15/1.01  
% 2.15/1.01  fof(f25,plain,(
% 2.15/1.01    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.15/1.01    inference(flattening,[],[f24])).
% 2.15/1.01  
% 2.15/1.01  fof(f62,plain,(
% 2.15/1.01    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.15/1.01    inference(cnf_transformation,[],[f25])).
% 2.15/1.01  
% 2.15/1.01  fof(f17,axiom,(
% 2.15/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.15/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.15/1.01  
% 2.15/1.01  fof(f34,plain,(
% 2.15/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.15/1.01    inference(ennf_transformation,[],[f17])).
% 2.15/1.01  
% 2.15/1.01  fof(f35,plain,(
% 2.15/1.01    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.15/1.01    inference(flattening,[],[f34])).
% 2.15/1.01  
% 2.15/1.01  fof(f48,plain,(
% 2.15/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.15/1.01    inference(nnf_transformation,[],[f35])).
% 2.15/1.01  
% 2.15/1.01  fof(f75,plain,(
% 2.15/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.15/1.01    inference(cnf_transformation,[],[f48])).
% 2.15/1.01  
% 2.15/1.01  fof(f82,plain,(
% 2.15/1.01    v1_funct_2(sK5,k1_tarski(sK3),sK4)),
% 2.15/1.01    inference(cnf_transformation,[],[f50])).
% 2.15/1.01  
% 2.15/1.01  fof(f94,plain,(
% 2.15/1.01    v1_funct_2(sK5,k2_enumset1(sK3,sK3,sK3,sK3),sK4)),
% 2.15/1.01    inference(definition_unfolding,[],[f82,f87])).
% 2.15/1.01  
% 2.15/1.01  fof(f84,plain,(
% 2.15/1.01    k1_xboole_0 != sK4),
% 2.15/1.01    inference(cnf_transformation,[],[f50])).
% 2.15/1.01  
% 2.15/1.01  fof(f15,axiom,(
% 2.15/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 2.15/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.15/1.01  
% 2.15/1.01  fof(f32,plain,(
% 2.15/1.01    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.15/1.01    inference(ennf_transformation,[],[f15])).
% 2.15/1.01  
% 2.15/1.01  fof(f41,plain,(
% 2.15/1.01    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.15/1.01    inference(nnf_transformation,[],[f32])).
% 2.15/1.01  
% 2.15/1.01  fof(f42,plain,(
% 2.15/1.01    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.15/1.01    inference(rectify,[],[f41])).
% 2.15/1.01  
% 2.15/1.01  fof(f44,plain,(
% 2.15/1.01    ! [X2,X1] : (? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)) => (! [X6] : ~r2_hidden(k4_tarski(sK1(X1,X2),X6),X2) & r2_hidden(sK1(X1,X2),X1)))),
% 2.15/1.01    introduced(choice_axiom,[])).
% 2.15/1.01  
% 2.15/1.01  fof(f43,plain,(
% 2.15/1.01    ! [X3,X2] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) => r2_hidden(k4_tarski(X3,sK0(X2,X3)),X2))),
% 2.15/1.01    introduced(choice_axiom,[])).
% 2.15/1.01  
% 2.15/1.01  fof(f45,plain,(
% 2.15/1.01    ! [X0,X1,X2] : (((! [X3] : (r2_hidden(k4_tarski(X3,sK0(X2,X3)),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | (! [X6] : ~r2_hidden(k4_tarski(sK1(X1,X2),X6),X2) & r2_hidden(sK1(X1,X2),X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.15/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f42,f44,f43])).
% 2.15/1.01  
% 2.15/1.01  fof(f71,plain,(
% 2.15/1.01    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X3,sK0(X2,X3)),X2) | ~r2_hidden(X3,X1) | k1_relset_1(X1,X0,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 2.15/1.01    inference(cnf_transformation,[],[f45])).
% 2.15/1.01  
% 2.15/1.01  fof(f6,axiom,(
% 2.15/1.01    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.15/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.15/1.01  
% 2.15/1.01  fof(f58,plain,(
% 2.15/1.01    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.15/1.01    inference(cnf_transformation,[],[f6])).
% 2.15/1.01  
% 2.15/1.01  fof(f1,axiom,(
% 2.15/1.01    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.15/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.15/1.01  
% 2.15/1.01  fof(f51,plain,(
% 2.15/1.01    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.15/1.01    inference(cnf_transformation,[],[f1])).
% 2.15/1.01  
% 2.15/1.01  fof(f11,axiom,(
% 2.15/1.01    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.15/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.15/1.01  
% 2.15/1.01  fof(f28,plain,(
% 2.15/1.01    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.15/1.01    inference(ennf_transformation,[],[f11])).
% 2.15/1.01  
% 2.15/1.01  fof(f65,plain,(
% 2.15/1.01    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.15/1.01    inference(cnf_transformation,[],[f28])).
% 2.15/1.01  
% 2.15/1.01  cnf(c_20,plain,
% 2.15/1.01      ( r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 2.15/1.01      inference(cnf_transformation,[],[f72]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_1115,plain,
% 2.15/1.01      ( k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0) = iProver_top ),
% 2.15/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_29,negated_conjecture,
% 2.15/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) ),
% 2.15/1.01      inference(cnf_transformation,[],[f93]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_1114,plain,
% 2.15/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) = iProver_top ),
% 2.15/1.01      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_3,plain,
% 2.15/1.01      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
% 2.15/1.01      | k2_enumset1(X1,X1,X1,X1) = X0
% 2.15/1.01      | k1_xboole_0 = X0 ),
% 2.15/1.01      inference(cnf_transformation,[],[f90]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_13,plain,
% 2.15/1.01      ( v4_relat_1(X0,X1)
% 2.15/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.15/1.01      inference(cnf_transformation,[],[f67]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_7,plain,
% 2.15/1.01      ( ~ v4_relat_1(X0,X1)
% 2.15/1.01      | r1_tarski(k1_relat_1(X0),X1)
% 2.15/1.01      | ~ v1_relat_1(X0) ),
% 2.15/1.01      inference(cnf_transformation,[],[f60]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_363,plain,
% 2.15/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.15/1.01      | r1_tarski(k1_relat_1(X0),X1)
% 2.15/1.01      | ~ v1_relat_1(X0) ),
% 2.15/1.01      inference(resolution,[status(thm)],[c_13,c_7]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_12,plain,
% 2.15/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.15/1.01      | v1_relat_1(X0) ),
% 2.15/1.01      inference(cnf_transformation,[],[f66]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_367,plain,
% 2.15/1.01      ( r1_tarski(k1_relat_1(X0),X1)
% 2.15/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.15/1.01      inference(global_propositional_subsumption,
% 2.15/1.01                [status(thm)],
% 2.15/1.01                [c_363,c_12]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_368,plain,
% 2.15/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.15/1.01      | r1_tarski(k1_relat_1(X0),X1) ),
% 2.15/1.01      inference(renaming,[status(thm)],[c_367]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_465,plain,
% 2.15/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.15/1.01      | k2_enumset1(X3,X3,X3,X3) != X1
% 2.15/1.01      | k2_enumset1(X3,X3,X3,X3) = X4
% 2.15/1.01      | k1_relat_1(X0) != X4
% 2.15/1.01      | k1_xboole_0 = X4 ),
% 2.15/1.01      inference(resolution_lifted,[status(thm)],[c_3,c_368]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_466,plain,
% 2.15/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2)))
% 2.15/1.01      | k2_enumset1(X1,X1,X1,X1) = k1_relat_1(X0)
% 2.15/1.01      | k1_xboole_0 = k1_relat_1(X0) ),
% 2.15/1.01      inference(unflattening,[status(thm)],[c_465]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_1110,plain,
% 2.15/1.01      ( k2_enumset1(X0,X0,X0,X0) = k1_relat_1(X1)
% 2.15/1.01      | k1_xboole_0 = k1_relat_1(X1)
% 2.15/1.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),X2))) != iProver_top ),
% 2.15/1.01      inference(predicate_to_equality,[status(thm)],[c_466]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_1876,plain,
% 2.15/1.01      ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_relat_1(sK5)
% 2.15/1.01      | k1_relat_1(sK5) = k1_xboole_0 ),
% 2.15/1.01      inference(superposition,[status(thm)],[c_1114,c_1110]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_27,negated_conjecture,
% 2.15/1.01      ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) ),
% 2.15/1.01      inference(cnf_transformation,[],[f92]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_1295,plain,
% 2.15/1.01      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))
% 2.15/1.01      | v1_relat_1(sK5) ),
% 2.15/1.01      inference(instantiation,[status(thm)],[c_12]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_14,plain,
% 2.15/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.15/1.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.15/1.01      inference(cnf_transformation,[],[f68]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_1308,plain,
% 2.15/1.01      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))
% 2.15/1.01      | k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_relat_1(sK5) ),
% 2.15/1.01      inference(instantiation,[status(thm)],[c_14]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_753,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_1301,plain,
% 2.15/1.01      ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != X0
% 2.15/1.01      | k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) = k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5)
% 2.15/1.01      | k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) != X0 ),
% 2.15/1.01      inference(instantiation,[status(thm)],[c_753]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_1374,plain,
% 2.15/1.01      ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) = k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5)
% 2.15/1.01      | k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relat_1(sK5)
% 2.15/1.01      | k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) != k2_relat_1(sK5) ),
% 2.15/1.01      inference(instantiation,[status(thm)],[c_1301]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_10,plain,
% 2.15/1.01      ( ~ v1_funct_1(X0)
% 2.15/1.01      | ~ v1_relat_1(X0)
% 2.15/1.01      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 2.15/1.01      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
% 2.15/1.01      inference(cnf_transformation,[],[f91]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_31,negated_conjecture,
% 2.15/1.01      ( v1_funct_1(sK5) ),
% 2.15/1.01      inference(cnf_transformation,[],[f81]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_344,plain,
% 2.15/1.01      ( ~ v1_relat_1(X0)
% 2.15/1.01      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 2.15/1.01      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
% 2.15/1.01      | sK5 != X0 ),
% 2.15/1.01      inference(resolution_lifted,[status(thm)],[c_10,c_31]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_345,plain,
% 2.15/1.01      ( ~ v1_relat_1(sK5)
% 2.15/1.01      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5)
% 2.15/1.01      | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5) ),
% 2.15/1.01      inference(unflattening,[status(thm)],[c_344]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_1410,plain,
% 2.15/1.01      ( ~ v1_relat_1(sK5)
% 2.15/1.01      | k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) = k2_relat_1(sK5)
% 2.15/1.01      | k2_enumset1(sK3,sK3,sK3,sK3) != k1_relat_1(sK5) ),
% 2.15/1.01      inference(instantiation,[status(thm)],[c_345]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_2179,plain,
% 2.15/1.01      ( k1_relat_1(sK5) = k1_xboole_0 ),
% 2.15/1.01      inference(global_propositional_subsumption,
% 2.15/1.01                [status(thm)],
% 2.15/1.01                [c_1876,c_29,c_27,c_1295,c_1308,c_1374,c_1410]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_9,plain,
% 2.15/1.01      ( ~ v1_relat_1(X0)
% 2.15/1.01      | k1_relat_1(X0) != k1_xboole_0
% 2.15/1.01      | k1_xboole_0 = X0 ),
% 2.15/1.01      inference(cnf_transformation,[],[f62]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_1123,plain,
% 2.15/1.01      ( k1_relat_1(X0) != k1_xboole_0
% 2.15/1.01      | k1_xboole_0 = X0
% 2.15/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.15/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_2190,plain,
% 2.15/1.01      ( sK5 = k1_xboole_0 | v1_relat_1(sK5) != iProver_top ),
% 2.15/1.01      inference(superposition,[status(thm)],[c_2179,c_1123]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_1389,plain,
% 2.15/1.01      ( ~ v1_relat_1(sK5)
% 2.15/1.01      | k1_relat_1(sK5) != k1_xboole_0
% 2.15/1.01      | k1_xboole_0 = sK5 ),
% 2.15/1.01      inference(instantiation,[status(thm)],[c_9]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_752,plain,( X0 = X0 ),theory(equality) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_1401,plain,
% 2.15/1.01      ( sK5 = sK5 ),
% 2.15/1.01      inference(instantiation,[status(thm)],[c_752]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_1717,plain,
% 2.15/1.01      ( sK5 != X0 | sK5 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 2.15/1.01      inference(instantiation,[status(thm)],[c_753]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_2127,plain,
% 2.15/1.01      ( sK5 != sK5 | sK5 = k1_xboole_0 | k1_xboole_0 != sK5 ),
% 2.15/1.01      inference(instantiation,[status(thm)],[c_1717]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_2193,plain,
% 2.15/1.01      ( sK5 = k1_xboole_0 ),
% 2.15/1.01      inference(global_propositional_subsumption,
% 2.15/1.01                [status(thm)],
% 2.15/1.01                [c_2190,c_29,c_27,c_1295,c_1308,c_1374,c_1389,c_1401,
% 2.15/1.01                 c_1410,c_1876,c_2127]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_26,plain,
% 2.15/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.15/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.15/1.01      | k1_relset_1(X1,X2,X0) = X1
% 2.15/1.01      | k1_xboole_0 = X2 ),
% 2.15/1.01      inference(cnf_transformation,[],[f75]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_30,negated_conjecture,
% 2.15/1.01      ( v1_funct_2(sK5,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
% 2.15/1.01      inference(cnf_transformation,[],[f94]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_548,plain,
% 2.15/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.15/1.01      | k2_enumset1(sK3,sK3,sK3,sK3) != X1
% 2.15/1.01      | k1_relset_1(X1,X2,X0) = X1
% 2.15/1.01      | sK4 != X2
% 2.15/1.01      | sK5 != X0
% 2.15/1.01      | k1_xboole_0 = X2 ),
% 2.15/1.01      inference(resolution_lifted,[status(thm)],[c_26,c_30]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_549,plain,
% 2.15/1.01      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))
% 2.15/1.01      | k1_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_enumset1(sK3,sK3,sK3,sK3)
% 2.15/1.01      | k1_xboole_0 = sK4 ),
% 2.15/1.01      inference(unflattening,[status(thm)],[c_548]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_28,negated_conjecture,
% 2.15/1.01      ( k1_xboole_0 != sK4 ),
% 2.15/1.01      inference(cnf_transformation,[],[f84]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_551,plain,
% 2.15/1.01      ( k1_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 2.15/1.01      inference(global_propositional_subsumption,
% 2.15/1.01                [status(thm)],
% 2.15/1.01                [c_549,c_29,c_28]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_2202,plain,
% 2.15/1.01      ( k1_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0) = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 2.15/1.01      inference(demodulation,[status(thm)],[c_2193,c_551]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_15,plain,
% 2.15/1.01      ( ~ r2_hidden(X0,X1)
% 2.15/1.01      | r2_hidden(k4_tarski(X0,sK0(X2,X0)),X2)
% 2.15/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.15/1.01      | k1_relset_1(X1,X3,X2) != X1 ),
% 2.15/1.01      inference(cnf_transformation,[],[f71]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_1120,plain,
% 2.15/1.01      ( k1_relset_1(X0,X1,X2) != X0
% 2.15/1.01      | r2_hidden(X3,X0) != iProver_top
% 2.15/1.01      | r2_hidden(k4_tarski(X3,sK0(X2,X3)),X2) = iProver_top
% 2.15/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.15/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_2713,plain,
% 2.15/1.01      ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top
% 2.15/1.01      | r2_hidden(k4_tarski(X0,sK0(k1_xboole_0,X0)),k1_xboole_0) = iProver_top
% 2.15/1.01      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) != iProver_top ),
% 2.15/1.01      inference(superposition,[status(thm)],[c_2202,c_1120]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_4,plain,
% 2.15/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.15/1.01      inference(cnf_transformation,[],[f58]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_1126,plain,
% 2.15/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.15/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_0,plain,
% 2.15/1.01      ( r1_tarski(k1_xboole_0,X0) ),
% 2.15/1.01      inference(cnf_transformation,[],[f51]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_11,plain,
% 2.15/1.01      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 2.15/1.01      inference(cnf_transformation,[],[f65]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_438,plain,
% 2.15/1.01      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 2.15/1.01      inference(resolution_lifted,[status(thm)],[c_0,c_11]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_439,plain,
% 2.15/1.01      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 2.15/1.01      inference(unflattening,[status(thm)],[c_438]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_1112,plain,
% 2.15/1.01      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.15/1.01      inference(predicate_to_equality,[status(thm)],[c_439]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_2887,plain,
% 2.15/1.01      ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top ),
% 2.15/1.01      inference(forward_subsumption_resolution,
% 2.15/1.01                [status(thm)],
% 2.15/1.01                [c_2713,c_1126,c_1112]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_2891,plain,
% 2.15/1.01      ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_xboole_0 ),
% 2.15/1.01      inference(superposition,[status(thm)],[c_1115,c_2887]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_1113,plain,
% 2.15/1.01      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5)
% 2.15/1.01      | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5)
% 2.15/1.01      | v1_relat_1(sK5) != iProver_top ),
% 2.15/1.01      inference(predicate_to_equality,[status(thm)],[c_345]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_34,plain,
% 2.15/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) = iProver_top ),
% 2.15/1.01      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_346,plain,
% 2.15/1.01      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5)
% 2.15/1.01      | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5)
% 2.15/1.01      | v1_relat_1(sK5) != iProver_top ),
% 2.15/1.01      inference(predicate_to_equality,[status(thm)],[c_345]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_1296,plain,
% 2.15/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) != iProver_top
% 2.15/1.01      | v1_relat_1(sK5) = iProver_top ),
% 2.15/1.01      inference(predicate_to_equality,[status(thm)],[c_1295]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_1334,plain,
% 2.15/1.01      ( k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5)
% 2.15/1.01      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5) ),
% 2.15/1.01      inference(global_propositional_subsumption,
% 2.15/1.01                [status(thm)],
% 2.15/1.01                [c_1113,c_34,c_346,c_1296]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_1335,plain,
% 2.15/1.01      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5)
% 2.15/1.01      | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5) ),
% 2.15/1.01      inference(renaming,[status(thm)],[c_1334]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_2183,plain,
% 2.15/1.01      ( k2_enumset1(X0,X0,X0,X0) != k1_xboole_0
% 2.15/1.01      | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5) ),
% 2.15/1.01      inference(demodulation,[status(thm)],[c_2179,c_1335]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_2806,plain,
% 2.15/1.01      ( k2_enumset1(X0,X0,X0,X0) != k1_xboole_0
% 2.15/1.01      | k2_enumset1(k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0)) = k2_relat_1(k1_xboole_0) ),
% 2.15/1.01      inference(light_normalisation,[status(thm)],[c_2183,c_2193]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_2911,plain,
% 2.15/1.01      ( k2_enumset1(k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3)) = k2_relat_1(k1_xboole_0) ),
% 2.15/1.01      inference(superposition,[status(thm)],[c_2891,c_2806]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_1121,plain,
% 2.15/1.01      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.15/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.15/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_1885,plain,
% 2.15/1.01      ( k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_relat_1(sK5) ),
% 2.15/1.01      inference(superposition,[status(thm)],[c_1114,c_1121]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_2069,plain,
% 2.15/1.01      ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relat_1(sK5) ),
% 2.15/1.01      inference(demodulation,[status(thm)],[c_1885,c_27]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_2198,plain,
% 2.15/1.01      ( k2_enumset1(k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3)) != k2_relat_1(k1_xboole_0) ),
% 2.15/1.01      inference(demodulation,[status(thm)],[c_2193,c_2069]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(contradiction,plain,
% 2.15/1.01      ( $false ),
% 2.15/1.01      inference(minisat,[status(thm)],[c_2911,c_2198]) ).
% 2.15/1.01  
% 2.15/1.01  
% 2.15/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.15/1.01  
% 2.15/1.01  ------                               Statistics
% 2.15/1.01  
% 2.15/1.01  ------ General
% 2.15/1.01  
% 2.15/1.01  abstr_ref_over_cycles:                  0
% 2.15/1.01  abstr_ref_under_cycles:                 0
% 2.15/1.01  gc_basic_clause_elim:                   0
% 2.15/1.01  forced_gc_time:                         0
% 2.15/1.01  parsing_time:                           0.01
% 2.15/1.01  unif_index_cands_time:                  0.
% 2.15/1.01  unif_index_add_time:                    0.
% 2.15/1.01  orderings_time:                         0.
% 2.15/1.01  out_proof_time:                         0.012
% 2.15/1.01  total_time:                             0.131
% 2.15/1.01  num_of_symbols:                         55
% 2.15/1.01  num_of_terms:                           2849
% 2.15/1.01  
% 2.15/1.01  ------ Preprocessing
% 2.15/1.01  
% 2.15/1.01  num_of_splits:                          0
% 2.15/1.01  num_of_split_atoms:                     0
% 2.15/1.01  num_of_reused_defs:                     0
% 2.15/1.01  num_eq_ax_congr_red:                    32
% 2.15/1.01  num_of_sem_filtered_clauses:            1
% 2.15/1.01  num_of_subtypes:                        0
% 2.15/1.01  monotx_restored_types:                  0
% 2.15/1.01  sat_num_of_epr_types:                   0
% 2.15/1.01  sat_num_of_non_cyclic_types:            0
% 2.15/1.01  sat_guarded_non_collapsed_types:        0
% 2.15/1.01  num_pure_diseq_elim:                    0
% 2.15/1.01  simp_replaced_by:                       0
% 2.15/1.01  res_preprocessed:                       130
% 2.15/1.01  prep_upred:                             0
% 2.15/1.01  prep_unflattend:                        44
% 2.15/1.01  smt_new_axioms:                         0
% 2.15/1.01  pred_elim_cands:                        3
% 2.15/1.01  pred_elim:                              4
% 2.15/1.01  pred_elim_cl:                           9
% 2.15/1.01  pred_elim_cycles:                       7
% 2.15/1.01  merged_defs:                            0
% 2.15/1.01  merged_defs_ncl:                        0
% 2.15/1.01  bin_hyper_res:                          0
% 2.15/1.01  prep_cycles:                            4
% 2.15/1.01  pred_elim_time:                         0.006
% 2.15/1.01  splitting_time:                         0.
% 2.15/1.01  sem_filter_time:                        0.
% 2.15/1.01  monotx_time:                            0.
% 2.15/1.01  subtype_inf_time:                       0.
% 2.15/1.01  
% 2.15/1.01  ------ Problem properties
% 2.15/1.01  
% 2.15/1.01  clauses:                                23
% 2.15/1.01  conjectures:                            3
% 2.15/1.01  epr:                                    2
% 2.15/1.01  horn:                                   19
% 2.15/1.01  ground:                                 6
% 2.15/1.01  unary:                                  7
% 2.15/1.01  binary:                                 4
% 2.15/1.01  lits:                                   53
% 2.15/1.01  lits_eq:                                25
% 2.15/1.01  fd_pure:                                0
% 2.15/1.01  fd_pseudo:                              0
% 2.15/1.01  fd_cond:                                5
% 2.15/1.01  fd_pseudo_cond:                         0
% 2.15/1.01  ac_symbols:                             0
% 2.15/1.01  
% 2.15/1.01  ------ Propositional Solver
% 2.15/1.01  
% 2.15/1.01  prop_solver_calls:                      28
% 2.15/1.01  prop_fast_solver_calls:                 784
% 2.15/1.01  smt_solver_calls:                       0
% 2.15/1.01  smt_fast_solver_calls:                  0
% 2.15/1.01  prop_num_of_clauses:                    976
% 2.15/1.01  prop_preprocess_simplified:             4479
% 2.15/1.01  prop_fo_subsumed:                       9
% 2.15/1.01  prop_solver_time:                       0.
% 2.15/1.01  smt_solver_time:                        0.
% 2.15/1.01  smt_fast_solver_time:                   0.
% 2.15/1.01  prop_fast_solver_time:                  0.
% 2.15/1.01  prop_unsat_core_time:                   0.
% 2.15/1.01  
% 2.15/1.01  ------ QBF
% 2.15/1.01  
% 2.15/1.01  qbf_q_res:                              0
% 2.15/1.01  qbf_num_tautologies:                    0
% 2.15/1.01  qbf_prep_cycles:                        0
% 2.15/1.01  
% 2.15/1.01  ------ BMC1
% 2.15/1.01  
% 2.15/1.01  bmc1_current_bound:                     -1
% 2.15/1.01  bmc1_last_solved_bound:                 -1
% 2.15/1.01  bmc1_unsat_core_size:                   -1
% 2.15/1.01  bmc1_unsat_core_parents_size:           -1
% 2.15/1.01  bmc1_merge_next_fun:                    0
% 2.15/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.15/1.01  
% 2.15/1.01  ------ Instantiation
% 2.15/1.01  
% 2.15/1.01  inst_num_of_clauses:                    358
% 2.15/1.01  inst_num_in_passive:                    161
% 2.15/1.01  inst_num_in_active:                     183
% 2.15/1.01  inst_num_in_unprocessed:                15
% 2.15/1.01  inst_num_of_loops:                      210
% 2.15/1.01  inst_num_of_learning_restarts:          0
% 2.15/1.01  inst_num_moves_active_passive:          24
% 2.15/1.01  inst_lit_activity:                      0
% 2.15/1.01  inst_lit_activity_moves:                0
% 2.15/1.01  inst_num_tautologies:                   0
% 2.15/1.01  inst_num_prop_implied:                  0
% 2.15/1.01  inst_num_existing_simplified:           0
% 2.15/1.01  inst_num_eq_res_simplified:             0
% 2.15/1.01  inst_num_child_elim:                    0
% 2.15/1.01  inst_num_of_dismatching_blockings:      73
% 2.15/1.01  inst_num_of_non_proper_insts:           221
% 2.15/1.01  inst_num_of_duplicates:                 0
% 2.15/1.01  inst_inst_num_from_inst_to_res:         0
% 2.15/1.01  inst_dismatching_checking_time:         0.
% 2.15/1.01  
% 2.15/1.01  ------ Resolution
% 2.15/1.01  
% 2.15/1.01  res_num_of_clauses:                     0
% 2.15/1.01  res_num_in_passive:                     0
% 2.15/1.01  res_num_in_active:                      0
% 2.15/1.01  res_num_of_loops:                       134
% 2.15/1.01  res_forward_subset_subsumed:            34
% 2.15/1.01  res_backward_subset_subsumed:           2
% 2.15/1.01  res_forward_subsumed:                   1
% 2.15/1.01  res_backward_subsumed:                  0
% 2.15/1.01  res_forward_subsumption_resolution:     0
% 2.15/1.01  res_backward_subsumption_resolution:    0
% 2.15/1.01  res_clause_to_clause_subsumption:       71
% 2.15/1.01  res_orphan_elimination:                 0
% 2.15/1.01  res_tautology_del:                      45
% 2.15/1.01  res_num_eq_res_simplified:              0
% 2.15/1.01  res_num_sel_changes:                    0
% 2.15/1.01  res_moves_from_active_to_pass:          0
% 2.15/1.01  
% 2.15/1.01  ------ Superposition
% 2.15/1.01  
% 2.15/1.01  sup_time_total:                         0.
% 2.15/1.01  sup_time_generating:                    0.
% 2.15/1.01  sup_time_sim_full:                      0.
% 2.15/1.01  sup_time_sim_immed:                     0.
% 2.15/1.01  
% 2.15/1.01  sup_num_of_clauses:                     30
% 2.15/1.01  sup_num_in_active:                      26
% 2.15/1.01  sup_num_in_passive:                     4
% 2.15/1.01  sup_num_of_loops:                       41
% 2.15/1.01  sup_fw_superposition:                   14
% 2.15/1.01  sup_bw_superposition:                   9
% 2.15/1.01  sup_immediate_simplified:               9
% 2.15/1.01  sup_given_eliminated:                   1
% 2.15/1.01  comparisons_done:                       0
% 2.15/1.01  comparisons_avoided:                    0
% 2.15/1.01  
% 2.15/1.01  ------ Simplifications
% 2.15/1.01  
% 2.15/1.01  
% 2.15/1.01  sim_fw_subset_subsumed:                 5
% 2.15/1.01  sim_bw_subset_subsumed:                 0
% 2.15/1.01  sim_fw_subsumed:                        4
% 2.15/1.01  sim_bw_subsumed:                        0
% 2.15/1.01  sim_fw_subsumption_res:                 3
% 2.15/1.01  sim_bw_subsumption_res:                 0
% 2.15/1.01  sim_tautology_del:                      0
% 2.15/1.01  sim_eq_tautology_del:                   1
% 2.15/1.01  sim_eq_res_simp:                        1
% 2.15/1.01  sim_fw_demodulated:                     0
% 2.15/1.01  sim_bw_demodulated:                     17
% 2.15/1.01  sim_light_normalised:                   3
% 2.15/1.01  sim_joinable_taut:                      0
% 2.15/1.01  sim_joinable_simp:                      0
% 2.15/1.01  sim_ac_normalised:                      0
% 2.15/1.01  sim_smt_subsumption:                    0
% 2.15/1.01  
%------------------------------------------------------------------------------
