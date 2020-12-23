%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:06:02 EST 2020

% Result     : Theorem 7.57s
% Output     : CNFRefutation 7.57s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 317 expanded)
%              Number of clauses        :   68 (  96 expanded)
%              Number of leaves         :   19 (  65 expanded)
%              Depth                    :   19
%              Number of atoms          :  457 (1103 expanded)
%              Number of equality atoms :  216 ( 414 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f35,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f36,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f35])).

fof(f49,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(X3,X2) != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
   => ( k1_funct_1(sK5,sK4) != sK3
      & r2_hidden(sK4,sK2)
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
      & v1_funct_2(sK5,sK2,k1_tarski(sK3))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( k1_funct_1(sK5,sK4) != sK3
    & r2_hidden(sK4,sK2)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
    & v1_funct_2(sK5,sK2,k1_tarski(sK3))
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f36,f49])).

fof(f88,plain,(
    r2_hidden(sK4,sK2) ),
    inference(cnf_transformation,[],[f50])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
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
    inference(flattening,[],[f33])).

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
    inference(nnf_transformation,[],[f34])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f86,plain,(
    v1_funct_2(sK5,sK2,k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f50])).

fof(f4,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f90,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f65,f66])).

fof(f91,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f64,f90])).

fof(f106,plain,(
    v1_funct_2(sK5,sK2,k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(definition_unfolding,[],[f86,f91])).

fof(f87,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) ),
    inference(cnf_transformation,[],[f50])).

fof(f105,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))) ),
    inference(definition_unfolding,[],[f87,f91])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f37])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK0(X0,X1,X2,X3) != X2
            & sK0(X0,X1,X2,X3) != X1
            & sK0(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
        & ( sK0(X0,X1,X2,X3) = X2
          | sK0(X0,X1,X2,X3) = X1
          | sK0(X0,X1,X2,X3) = X0
          | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK0(X0,X1,X2,X3) != X2
              & sK0(X0,X1,X2,X3) != X1
              & sK0(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
          & ( sK0(X0,X1,X2,X3) = X2
            | sK0(X0,X1,X2,X3) = X1
            | sK0(X0,X1,X2,X3) = X0
            | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).

fof(f53,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f98,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f53,f66])).

fof(f111,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f98])).

fof(f112,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k2_enumset1(X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f111])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f85,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f50])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f104,plain,(
    ! [X0] : ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
    inference(definition_unfolding,[],[f67,f91])).

fof(f52,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f99,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f52,f66])).

fof(f113,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k2_enumset1(X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f99])).

fof(f89,plain,(
    k1_funct_1(sK5,sK4) != sK3 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_32,negated_conjecture,
    ( r2_hidden(sK4,sK2) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_22907,plain,
    ( r2_hidden(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK5,sK2,k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_650,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_enumset1(sK3,sK3,sK3,sK3) != X2
    | k1_relset_1(X1,X2,X0) = X1
    | sK2 != X1
    | sK5 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_34])).

cnf(c_651,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))))
    | k1_relset_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK5) = sK2
    | k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(unflattening,[status(thm)],[c_650])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_653,plain,
    ( k1_relset_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK5) = sK2
    | k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_651,c_33])).

cnf(c_22906,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_22908,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23214,plain,
    ( k1_relset_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_22906,c_22908])).

cnf(c_23255,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_xboole_0
    | k1_relat_1(sK5) = sK2 ),
    inference(superposition,[status(thm)],[c_653,c_23214])).

cnf(c_7,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_22915,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_23286,plain,
    ( k1_relat_1(sK5) = sK2
    | r2_hidden(sK3,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_23255,c_22915])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_21,negated_conjecture,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_545,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_21])).

cnf(c_546,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_545])).

cnf(c_22901,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_546])).

cnf(c_23453,plain,
    ( k1_relat_1(sK5) = sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_23286,c_22901])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_476,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_35])).

cnf(c_477,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK5))
    | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5))
    | ~ v1_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_476])).

cnf(c_516,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(sK5))
    | r2_hidden(k1_funct_1(sK5,X3),k2_relat_1(sK5))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_477])).

cnf(c_517,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r2_hidden(X2,k1_relat_1(sK5))
    | r2_hidden(k1_funct_1(sK5,X2),k2_relat_1(sK5)) ),
    inference(unflattening,[status(thm)],[c_516])).

cnf(c_858,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK5))
    | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_517])).

cnf(c_22895,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_858])).

cnf(c_860,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_517])).

cnf(c_893,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_860])).

cnf(c_897,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_858])).

cnf(c_859,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_517])).

cnf(c_22894,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_859])).

cnf(c_23102,plain,
    ( sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_22906,c_22894])).

cnf(c_23155,plain,
    ( r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22895,c_893,c_897,c_23102])).

cnf(c_23156,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) = iProver_top ),
    inference(renaming,[status(thm)],[c_23155])).

cnf(c_23455,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_23453,c_23156])).

cnf(c_15,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_270,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_15])).

cnf(c_271,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_270])).

cnf(c_23,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_19,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_495,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_23,c_19])).

cnf(c_499,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_495,c_22])).

cnf(c_500,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_499])).

cnf(c_564,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | X4 != X1
    | k2_relat_1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_271,c_500])).

cnf(c_565,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relat_1(X0),k1_zfmisc_1(X2)) ),
    inference(unflattening,[status(thm)],[c_564])).

cnf(c_22899,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relat_1(X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_565])).

cnf(c_23201,plain,
    ( m1_subset_1(k2_relat_1(sK5),k1_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_22906,c_22899])).

cnf(c_17,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_22909,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_23241,plain,
    ( m1_subset_1(X0,k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_23201,c_22909])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_22910,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_23489,plain,
    ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top
    | v1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_23241,c_22910])).

cnf(c_13,negated_conjecture,
    ( ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_22911,plain,
    ( v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_23525,plain,
    ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_23489,c_22911])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f113])).

cnf(c_22914,plain,
    ( X0 = X1
    | X0 = X2
    | X0 = X3
    | r2_hidden(X0,k2_enumset1(X1,X1,X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_23530,plain,
    ( sK3 = X0
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_23525,c_22914])).

cnf(c_23566,plain,
    ( k1_funct_1(sK5,X0) = sK3
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_23455,c_23530])).

cnf(c_23594,plain,
    ( k1_funct_1(sK5,sK4) = sK3 ),
    inference(superposition,[status(thm)],[c_22907,c_23566])).

cnf(c_31,negated_conjecture,
    ( k1_funct_1(sK5,sK4) != sK3 ),
    inference(cnf_transformation,[],[f89])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_23594,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:43:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.57/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.57/1.50  
% 7.57/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.57/1.50  
% 7.57/1.50  ------  iProver source info
% 7.57/1.50  
% 7.57/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.57/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.57/1.50  git: non_committed_changes: false
% 7.57/1.50  git: last_make_outside_of_git: false
% 7.57/1.50  
% 7.57/1.50  ------ 
% 7.57/1.50  ------ Parsing...
% 7.57/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.57/1.50  
% 7.57/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 7.57/1.50  
% 7.57/1.50  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.57/1.50  
% 7.57/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.57/1.50  ------ Proving...
% 7.57/1.50  ------ Problem Properties 
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  clauses                                 30
% 7.57/1.50  conjectures                             4
% 7.57/1.50  EPR                                     4
% 7.57/1.50  Horn                                    23
% 7.57/1.50  unary                                   10
% 7.57/1.50  binary                                  8
% 7.57/1.50  lits                                    66
% 7.57/1.50  lits eq                                 27
% 7.57/1.50  fd_pure                                 0
% 7.57/1.50  fd_pseudo                               0
% 7.57/1.50  fd_cond                                 0
% 7.57/1.50  fd_pseudo_cond                          6
% 7.57/1.50  AC symbols                              0
% 7.57/1.50  
% 7.57/1.50  ------ Input Options Time Limit: Unbounded
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  ------ Preprocessing...
% 7.57/1.50  
% 7.57/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e ------ 
% 7.57/1.50  Current options:
% 7.57/1.50  ------ 
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  ------ Proving...
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.57/1.50  
% 7.57/1.50  ------ Proving...
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.57/1.50  
% 7.57/1.50  ------ Proving...
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.57/1.50  
% 7.57/1.50  ------ Proving...
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.57/1.50  
% 7.57/1.50  ------ Proving...
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.57/1.50  
% 7.57/1.50  ------ Proving...
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.57/1.50  
% 7.57/1.50  ------ Proving...
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.57/1.50  
% 7.57/1.50  ------ Proving...
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.57/1.50  
% 7.57/1.50  ------ Proving...
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.57/1.50  
% 7.57/1.50  ------ Proving...
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.57/1.50  
% 7.57/1.50  ------ Proving...
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.57/1.50  
% 7.57/1.50  ------ Proving...
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  ------ Preprocessing...
% 7.57/1.50  
% 7.57/1.50  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.57/1.50  
% 7.57/1.50  ------ Proving...
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  ------ Preprocessing...
% 7.57/1.50  
% 7.57/1.50  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.57/1.50  
% 7.57/1.50  ------ Proving...
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  ------ Preprocessing...
% 7.57/1.50  
% 7.57/1.50  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.57/1.50  
% 7.57/1.50  ------ Proving...
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.57/1.50  
% 7.57/1.50  ------ Proving...
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.57/1.50  
% 7.57/1.50  ------ Proving...
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.57/1.50  
% 7.57/1.50  ------ Proving...
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.57/1.50  
% 7.57/1.50  ------ Proving...
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.57/1.50  
% 7.57/1.50  ------ Proving...
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.57/1.50  
% 7.57/1.50  ------ Proving...
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.57/1.50  
% 7.57/1.50  ------ Proving...
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.57/1.50  
% 7.57/1.50  ------ Proving...
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.57/1.50  
% 7.57/1.50  ------ Proving...
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.57/1.50  
% 7.57/1.50  ------ Proving...
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.57/1.50  
% 7.57/1.50  ------ Proving...
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  ------ Preprocessing...
% 7.57/1.50  
% 7.57/1.50  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.57/1.50  
% 7.57/1.50  ------ Proving...
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  ------ Preprocessing...
% 7.57/1.50  
% 7.57/1.50  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.57/1.50  
% 7.57/1.50  ------ Proving...
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  ------ Preprocessing...
% 7.57/1.50  
% 7.57/1.50  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.57/1.50  
% 7.57/1.50  ------ Proving...
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.57/1.50  
% 7.57/1.50  ------ Proving...
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.57/1.50  
% 7.57/1.50  ------ Proving...
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.57/1.50  
% 7.57/1.50  ------ Proving...
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.57/1.50  
% 7.57/1.50  ------ Proving...
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.57/1.50  
% 7.57/1.50  ------ Proving...
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.57/1.50  
% 7.57/1.50  ------ Proving...
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.57/1.50  
% 7.57/1.50  ------ Proving...
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.57/1.50  
% 7.57/1.50  ------ Proving...
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.57/1.50  
% 7.57/1.50  ------ Proving...
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  ------ Preprocessing... sf_s  rm: 11 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.57/1.50  
% 7.57/1.50  ------ Proving...
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.57/1.50  
% 7.57/1.50  ------ Proving...
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.57/1.50  
% 7.57/1.50  ------ Proving...
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.57/1.50  
% 7.57/1.50  ------ Proving...
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.57/1.50  
% 7.57/1.50  ------ Proving...
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.57/1.50  
% 7.57/1.50  ------ Proving...
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  ------ Preprocessing... sf_s  rm: 10 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.57/1.50  
% 7.57/1.50  ------ Proving...
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.57/1.50  
% 7.57/1.50  ------ Proving...
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  % SZS status Theorem for theBenchmark.p
% 7.57/1.50  
% 7.57/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.57/1.50  
% 7.57/1.50  fof(f18,conjecture,(
% 7.57/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 7.57/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.50  
% 7.57/1.50  fof(f19,negated_conjecture,(
% 7.57/1.50    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 7.57/1.50    inference(negated_conjecture,[],[f18])).
% 7.57/1.50  
% 7.57/1.50  fof(f35,plain,(
% 7.57/1.50    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 7.57/1.50    inference(ennf_transformation,[],[f19])).
% 7.57/1.50  
% 7.57/1.50  fof(f36,plain,(
% 7.57/1.50    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 7.57/1.50    inference(flattening,[],[f35])).
% 7.57/1.50  
% 7.57/1.50  fof(f49,plain,(
% 7.57/1.50    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (k1_funct_1(sK5,sK4) != sK3 & r2_hidden(sK4,sK2) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) & v1_funct_2(sK5,sK2,k1_tarski(sK3)) & v1_funct_1(sK5))),
% 7.57/1.50    introduced(choice_axiom,[])).
% 7.57/1.50  
% 7.57/1.50  fof(f50,plain,(
% 7.57/1.50    k1_funct_1(sK5,sK4) != sK3 & r2_hidden(sK4,sK2) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) & v1_funct_2(sK5,sK2,k1_tarski(sK3)) & v1_funct_1(sK5)),
% 7.57/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f36,f49])).
% 7.57/1.50  
% 7.57/1.50  fof(f88,plain,(
% 7.57/1.50    r2_hidden(sK4,sK2)),
% 7.57/1.50    inference(cnf_transformation,[],[f50])).
% 7.57/1.50  
% 7.57/1.50  fof(f17,axiom,(
% 7.57/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.57/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.50  
% 7.57/1.50  fof(f33,plain,(
% 7.57/1.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.57/1.50    inference(ennf_transformation,[],[f17])).
% 7.57/1.50  
% 7.57/1.50  fof(f34,plain,(
% 7.57/1.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.57/1.50    inference(flattening,[],[f33])).
% 7.57/1.50  
% 7.57/1.50  fof(f48,plain,(
% 7.57/1.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.57/1.50    inference(nnf_transformation,[],[f34])).
% 7.57/1.50  
% 7.57/1.50  fof(f79,plain,(
% 7.57/1.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.57/1.50    inference(cnf_transformation,[],[f48])).
% 7.57/1.50  
% 7.57/1.50  fof(f86,plain,(
% 7.57/1.50    v1_funct_2(sK5,sK2,k1_tarski(sK3))),
% 7.57/1.50    inference(cnf_transformation,[],[f50])).
% 7.57/1.50  
% 7.57/1.50  fof(f4,axiom,(
% 7.57/1.50    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 7.57/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.50  
% 7.57/1.50  fof(f64,plain,(
% 7.57/1.50    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 7.57/1.50    inference(cnf_transformation,[],[f4])).
% 7.57/1.50  
% 7.57/1.50  fof(f5,axiom,(
% 7.57/1.50    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 7.57/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.50  
% 7.57/1.50  fof(f65,plain,(
% 7.57/1.50    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.57/1.50    inference(cnf_transformation,[],[f5])).
% 7.57/1.50  
% 7.57/1.50  fof(f6,axiom,(
% 7.57/1.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.57/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.50  
% 7.57/1.50  fof(f66,plain,(
% 7.57/1.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.57/1.50    inference(cnf_transformation,[],[f6])).
% 7.57/1.50  
% 7.57/1.50  fof(f90,plain,(
% 7.57/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 7.57/1.50    inference(definition_unfolding,[],[f65,f66])).
% 7.57/1.50  
% 7.57/1.50  fof(f91,plain,(
% 7.57/1.50    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 7.57/1.50    inference(definition_unfolding,[],[f64,f90])).
% 7.57/1.50  
% 7.57/1.50  fof(f106,plain,(
% 7.57/1.50    v1_funct_2(sK5,sK2,k2_enumset1(sK3,sK3,sK3,sK3))),
% 7.57/1.50    inference(definition_unfolding,[],[f86,f91])).
% 7.57/1.50  
% 7.57/1.50  fof(f87,plain,(
% 7.57/1.50    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))),
% 7.57/1.50    inference(cnf_transformation,[],[f50])).
% 7.57/1.50  
% 7.57/1.50  fof(f105,plain,(
% 7.57/1.50    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))))),
% 7.57/1.50    inference(definition_unfolding,[],[f87,f91])).
% 7.57/1.50  
% 7.57/1.50  fof(f16,axiom,(
% 7.57/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.57/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.50  
% 7.57/1.50  fof(f32,plain,(
% 7.57/1.50    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.57/1.50    inference(ennf_transformation,[],[f16])).
% 7.57/1.50  
% 7.57/1.50  fof(f78,plain,(
% 7.57/1.50    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.57/1.50    inference(cnf_transformation,[],[f32])).
% 7.57/1.50  
% 7.57/1.50  fof(f2,axiom,(
% 7.57/1.50    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 7.57/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.50  
% 7.57/1.50  fof(f21,plain,(
% 7.57/1.50    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 7.57/1.50    inference(ennf_transformation,[],[f2])).
% 7.57/1.50  
% 7.57/1.50  fof(f37,plain,(
% 7.57/1.50    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.57/1.50    inference(nnf_transformation,[],[f21])).
% 7.57/1.50  
% 7.57/1.50  fof(f38,plain,(
% 7.57/1.50    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.57/1.50    inference(flattening,[],[f37])).
% 7.57/1.50  
% 7.57/1.50  fof(f39,plain,(
% 7.57/1.50    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.57/1.50    inference(rectify,[],[f38])).
% 7.57/1.50  
% 7.57/1.50  fof(f40,plain,(
% 7.57/1.50    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 7.57/1.50    introduced(choice_axiom,[])).
% 7.57/1.50  
% 7.57/1.50  fof(f41,plain,(
% 7.57/1.50    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.57/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).
% 7.57/1.50  
% 7.57/1.50  fof(f53,plain,(
% 7.57/1.50    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 7.57/1.50    inference(cnf_transformation,[],[f41])).
% 7.57/1.50  
% 7.57/1.50  fof(f98,plain,(
% 7.57/1.50    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 7.57/1.50    inference(definition_unfolding,[],[f53,f66])).
% 7.57/1.50  
% 7.57/1.50  fof(f111,plain,(
% 7.57/1.50    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X5,X5,X1,X2) != X3) )),
% 7.57/1.50    inference(equality_resolution,[],[f98])).
% 7.57/1.50  
% 7.57/1.50  fof(f112,plain,(
% 7.57/1.50    ( ! [X2,X5,X1] : (r2_hidden(X5,k2_enumset1(X5,X5,X1,X2))) )),
% 7.57/1.50    inference(equality_resolution,[],[f111])).
% 7.57/1.50  
% 7.57/1.50  fof(f1,axiom,(
% 7.57/1.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.57/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.50  
% 7.57/1.50  fof(f51,plain,(
% 7.57/1.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.57/1.50    inference(cnf_transformation,[],[f1])).
% 7.57/1.50  
% 7.57/1.50  fof(f13,axiom,(
% 7.57/1.50    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 7.57/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.50  
% 7.57/1.50  fof(f29,plain,(
% 7.57/1.50    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 7.57/1.50    inference(ennf_transformation,[],[f13])).
% 7.57/1.50  
% 7.57/1.50  fof(f75,plain,(
% 7.57/1.50    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 7.57/1.50    inference(cnf_transformation,[],[f29])).
% 7.57/1.50  
% 7.57/1.50  fof(f14,axiom,(
% 7.57/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.57/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.50  
% 7.57/1.50  fof(f30,plain,(
% 7.57/1.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.57/1.50    inference(ennf_transformation,[],[f14])).
% 7.57/1.50  
% 7.57/1.50  fof(f76,plain,(
% 7.57/1.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.57/1.50    inference(cnf_transformation,[],[f30])).
% 7.57/1.50  
% 7.57/1.50  fof(f12,axiom,(
% 7.57/1.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 7.57/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.50  
% 7.57/1.50  fof(f27,plain,(
% 7.57/1.50    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.57/1.50    inference(ennf_transformation,[],[f12])).
% 7.57/1.50  
% 7.57/1.50  fof(f28,plain,(
% 7.57/1.50    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.57/1.50    inference(flattening,[],[f27])).
% 7.57/1.50  
% 7.57/1.50  fof(f74,plain,(
% 7.57/1.50    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.57/1.50    inference(cnf_transformation,[],[f28])).
% 7.57/1.50  
% 7.57/1.50  fof(f85,plain,(
% 7.57/1.50    v1_funct_1(sK5)),
% 7.57/1.50    inference(cnf_transformation,[],[f50])).
% 7.57/1.50  
% 7.57/1.50  fof(f9,axiom,(
% 7.57/1.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.57/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.50  
% 7.57/1.50  fof(f46,plain,(
% 7.57/1.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.57/1.50    inference(nnf_transformation,[],[f9])).
% 7.57/1.50  
% 7.57/1.50  fof(f70,plain,(
% 7.57/1.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.57/1.50    inference(cnf_transformation,[],[f46])).
% 7.57/1.50  
% 7.57/1.50  fof(f15,axiom,(
% 7.57/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.57/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.50  
% 7.57/1.50  fof(f20,plain,(
% 7.57/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 7.57/1.50    inference(pure_predicate_removal,[],[f15])).
% 7.57/1.50  
% 7.57/1.50  fof(f31,plain,(
% 7.57/1.50    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.57/1.50    inference(ennf_transformation,[],[f20])).
% 7.57/1.50  
% 7.57/1.50  fof(f77,plain,(
% 7.57/1.50    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.57/1.50    inference(cnf_transformation,[],[f31])).
% 7.57/1.50  
% 7.57/1.50  fof(f11,axiom,(
% 7.57/1.50    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 7.57/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.50  
% 7.57/1.50  fof(f26,plain,(
% 7.57/1.50    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.57/1.50    inference(ennf_transformation,[],[f11])).
% 7.57/1.50  
% 7.57/1.50  fof(f47,plain,(
% 7.57/1.50    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.57/1.50    inference(nnf_transformation,[],[f26])).
% 7.57/1.50  
% 7.57/1.50  fof(f72,plain,(
% 7.57/1.50    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.57/1.50    inference(cnf_transformation,[],[f47])).
% 7.57/1.50  
% 7.57/1.50  fof(f10,axiom,(
% 7.57/1.50    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 7.57/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.50  
% 7.57/1.50  fof(f24,plain,(
% 7.57/1.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 7.57/1.50    inference(ennf_transformation,[],[f10])).
% 7.57/1.50  
% 7.57/1.50  fof(f25,plain,(
% 7.57/1.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 7.57/1.50    inference(flattening,[],[f24])).
% 7.57/1.50  
% 7.57/1.50  fof(f71,plain,(
% 7.57/1.50    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 7.57/1.50    inference(cnf_transformation,[],[f25])).
% 7.57/1.50  
% 7.57/1.50  fof(f8,axiom,(
% 7.57/1.50    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 7.57/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.50  
% 7.57/1.50  fof(f22,plain,(
% 7.57/1.50    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 7.57/1.50    inference(ennf_transformation,[],[f8])).
% 7.57/1.50  
% 7.57/1.50  fof(f23,plain,(
% 7.57/1.50    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 7.57/1.50    inference(flattening,[],[f22])).
% 7.57/1.50  
% 7.57/1.50  fof(f68,plain,(
% 7.57/1.50    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 7.57/1.50    inference(cnf_transformation,[],[f23])).
% 7.57/1.50  
% 7.57/1.50  fof(f7,axiom,(
% 7.57/1.50    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 7.57/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.50  
% 7.57/1.50  fof(f67,plain,(
% 7.57/1.50    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 7.57/1.50    inference(cnf_transformation,[],[f7])).
% 7.57/1.50  
% 7.57/1.50  fof(f104,plain,(
% 7.57/1.50    ( ! [X0] : (~v1_xboole_0(k2_enumset1(X0,X0,X0,X0))) )),
% 7.57/1.50    inference(definition_unfolding,[],[f67,f91])).
% 7.57/1.50  
% 7.57/1.50  fof(f52,plain,(
% 7.57/1.50    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 7.57/1.50    inference(cnf_transformation,[],[f41])).
% 7.57/1.50  
% 7.57/1.50  fof(f99,plain,(
% 7.57/1.50    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 7.57/1.50    inference(definition_unfolding,[],[f52,f66])).
% 7.57/1.50  
% 7.57/1.50  fof(f113,plain,(
% 7.57/1.50    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k2_enumset1(X0,X0,X1,X2))) )),
% 7.57/1.50    inference(equality_resolution,[],[f99])).
% 7.57/1.50  
% 7.57/1.50  fof(f89,plain,(
% 7.57/1.50    k1_funct_1(sK5,sK4) != sK3),
% 7.57/1.50    inference(cnf_transformation,[],[f50])).
% 7.57/1.50  
% 7.57/1.50  cnf(c_32,negated_conjecture,
% 7.57/1.50      ( r2_hidden(sK4,sK2) ),
% 7.57/1.50      inference(cnf_transformation,[],[f88]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_22907,plain,
% 7.57/1.50      ( r2_hidden(sK4,sK2) = iProver_top ),
% 7.57/1.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_30,plain,
% 7.57/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.57/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.57/1.50      | k1_relset_1(X1,X2,X0) = X1
% 7.57/1.50      | k1_xboole_0 = X2 ),
% 7.57/1.50      inference(cnf_transformation,[],[f79]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_34,negated_conjecture,
% 7.57/1.50      ( v1_funct_2(sK5,sK2,k2_enumset1(sK3,sK3,sK3,sK3)) ),
% 7.57/1.50      inference(cnf_transformation,[],[f106]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_650,plain,
% 7.57/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.57/1.50      | k2_enumset1(sK3,sK3,sK3,sK3) != X2
% 7.57/1.50      | k1_relset_1(X1,X2,X0) = X1
% 7.57/1.50      | sK2 != X1
% 7.57/1.50      | sK5 != X0
% 7.57/1.50      | k1_xboole_0 = X2 ),
% 7.57/1.50      inference(resolution_lifted,[status(thm)],[c_30,c_34]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_651,plain,
% 7.57/1.50      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))))
% 7.57/1.50      | k1_relset_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK5) = sK2
% 7.57/1.50      | k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 7.57/1.50      inference(unflattening,[status(thm)],[c_650]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_33,negated_conjecture,
% 7.57/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))) ),
% 7.57/1.50      inference(cnf_transformation,[],[f105]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_653,plain,
% 7.57/1.50      ( k1_relset_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK5) = sK2
% 7.57/1.50      | k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 7.57/1.50      inference(global_propositional_subsumption,
% 7.57/1.50                [status(thm)],
% 7.57/1.50                [c_651,c_33]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_22906,plain,
% 7.57/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))) = iProver_top ),
% 7.57/1.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_24,plain,
% 7.57/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.57/1.50      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.57/1.50      inference(cnf_transformation,[],[f78]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_22908,plain,
% 7.57/1.50      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.57/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.57/1.50      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_23214,plain,
% 7.57/1.50      ( k1_relset_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK5) = k1_relat_1(sK5) ),
% 7.57/1.50      inference(superposition,[status(thm)],[c_22906,c_22908]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_23255,plain,
% 7.57/1.50      ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_xboole_0
% 7.57/1.50      | k1_relat_1(sK5) = sK2 ),
% 7.57/1.50      inference(superposition,[status(thm)],[c_653,c_23214]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_7,plain,
% 7.57/1.50      ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
% 7.57/1.50      inference(cnf_transformation,[],[f112]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_22915,plain,
% 7.57/1.50      ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) = iProver_top ),
% 7.57/1.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_23286,plain,
% 7.57/1.50      ( k1_relat_1(sK5) = sK2
% 7.57/1.50      | r2_hidden(sK3,k1_xboole_0) = iProver_top ),
% 7.57/1.50      inference(superposition,[status(thm)],[c_23255,c_22915]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_0,plain,
% 7.57/1.50      ( r1_tarski(k1_xboole_0,X0) ),
% 7.57/1.50      inference(cnf_transformation,[],[f51]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_21,negated_conjecture,
% 7.57/1.50      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 7.57/1.50      inference(cnf_transformation,[],[f75]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_545,plain,
% 7.57/1.50      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 7.57/1.50      inference(resolution_lifted,[status(thm)],[c_0,c_21]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_546,plain,
% 7.57/1.50      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 7.57/1.50      inference(unflattening,[status(thm)],[c_545]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_22901,plain,
% 7.57/1.50      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.57/1.50      inference(predicate_to_equality,[status(thm)],[c_546]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_23453,plain,
% 7.57/1.50      ( k1_relat_1(sK5) = sK2 ),
% 7.57/1.50      inference(forward_subsumption_resolution,
% 7.57/1.50                [status(thm)],
% 7.57/1.50                [c_23286,c_22901]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_22,plain,
% 7.57/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.57/1.50      | v1_relat_1(X0) ),
% 7.57/1.50      inference(cnf_transformation,[],[f76]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_20,plain,
% 7.57/1.50      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.57/1.50      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 7.57/1.50      | ~ v1_funct_1(X1)
% 7.57/1.50      | ~ v1_relat_1(X1) ),
% 7.57/1.50      inference(cnf_transformation,[],[f74]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_35,negated_conjecture,
% 7.57/1.50      ( v1_funct_1(sK5) ),
% 7.57/1.50      inference(cnf_transformation,[],[f85]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_476,plain,
% 7.57/1.50      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.57/1.50      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 7.57/1.50      | ~ v1_relat_1(X1)
% 7.57/1.50      | sK5 != X1 ),
% 7.57/1.50      inference(resolution_lifted,[status(thm)],[c_20,c_35]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_477,plain,
% 7.57/1.50      ( ~ r2_hidden(X0,k1_relat_1(sK5))
% 7.57/1.50      | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5))
% 7.57/1.50      | ~ v1_relat_1(sK5) ),
% 7.57/1.50      inference(unflattening,[status(thm)],[c_476]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_516,plain,
% 7.57/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.57/1.50      | ~ r2_hidden(X3,k1_relat_1(sK5))
% 7.57/1.50      | r2_hidden(k1_funct_1(sK5,X3),k2_relat_1(sK5))
% 7.57/1.50      | sK5 != X0 ),
% 7.57/1.50      inference(resolution_lifted,[status(thm)],[c_22,c_477]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_517,plain,
% 7.57/1.50      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.57/1.50      | ~ r2_hidden(X2,k1_relat_1(sK5))
% 7.57/1.50      | r2_hidden(k1_funct_1(sK5,X2),k2_relat_1(sK5)) ),
% 7.57/1.50      inference(unflattening,[status(thm)],[c_516]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_858,plain,
% 7.57/1.50      ( ~ r2_hidden(X0,k1_relat_1(sK5))
% 7.57/1.50      | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5))
% 7.57/1.50      | ~ sP0_iProver_split ),
% 7.57/1.50      inference(splitting,
% 7.57/1.50                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 7.57/1.50                [c_517]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_22895,plain,
% 7.57/1.50      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 7.57/1.50      | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) = iProver_top
% 7.57/1.50      | sP0_iProver_split != iProver_top ),
% 7.57/1.50      inference(predicate_to_equality,[status(thm)],[c_858]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_860,plain,
% 7.57/1.50      ( sP1_iProver_split | sP0_iProver_split ),
% 7.57/1.50      inference(splitting,
% 7.57/1.50                [splitting(split),new_symbols(definition,[])],
% 7.57/1.50                [c_517]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_893,plain,
% 7.57/1.50      ( sP1_iProver_split = iProver_top
% 7.57/1.50      | sP0_iProver_split = iProver_top ),
% 7.57/1.50      inference(predicate_to_equality,[status(thm)],[c_860]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_897,plain,
% 7.57/1.50      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 7.57/1.50      | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) = iProver_top
% 7.57/1.50      | sP0_iProver_split != iProver_top ),
% 7.57/1.50      inference(predicate_to_equality,[status(thm)],[c_858]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_859,plain,
% 7.57/1.50      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.57/1.50      | ~ sP1_iProver_split ),
% 7.57/1.50      inference(splitting,
% 7.57/1.50                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 7.57/1.50                [c_517]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_22894,plain,
% 7.57/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.57/1.50      | sP1_iProver_split != iProver_top ),
% 7.57/1.50      inference(predicate_to_equality,[status(thm)],[c_859]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_23102,plain,
% 7.57/1.50      ( sP1_iProver_split != iProver_top ),
% 7.57/1.50      inference(superposition,[status(thm)],[c_22906,c_22894]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_23155,plain,
% 7.57/1.50      ( r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) = iProver_top
% 7.57/1.50      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 7.57/1.50      inference(global_propositional_subsumption,
% 7.57/1.50                [status(thm)],
% 7.57/1.50                [c_22895,c_893,c_897,c_23102]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_23156,plain,
% 7.57/1.50      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 7.57/1.50      | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) = iProver_top ),
% 7.57/1.50      inference(renaming,[status(thm)],[c_23155]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_23455,plain,
% 7.57/1.50      ( r2_hidden(X0,sK2) != iProver_top
% 7.57/1.50      | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) = iProver_top ),
% 7.57/1.50      inference(demodulation,[status(thm)],[c_23453,c_23156]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_15,plain,
% 7.57/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.57/1.50      inference(cnf_transformation,[],[f70]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_270,plain,
% 7.57/1.50      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.57/1.50      inference(prop_impl,[status(thm)],[c_15]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_271,plain,
% 7.57/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.57/1.50      inference(renaming,[status(thm)],[c_270]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_23,plain,
% 7.57/1.50      ( v5_relat_1(X0,X1)
% 7.57/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 7.57/1.50      inference(cnf_transformation,[],[f77]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_19,plain,
% 7.57/1.50      ( ~ v5_relat_1(X0,X1)
% 7.57/1.50      | r1_tarski(k2_relat_1(X0),X1)
% 7.57/1.50      | ~ v1_relat_1(X0) ),
% 7.57/1.50      inference(cnf_transformation,[],[f72]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_495,plain,
% 7.57/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.57/1.50      | r1_tarski(k2_relat_1(X0),X2)
% 7.57/1.50      | ~ v1_relat_1(X0) ),
% 7.57/1.50      inference(resolution,[status(thm)],[c_23,c_19]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_499,plain,
% 7.57/1.50      ( r1_tarski(k2_relat_1(X0),X2)
% 7.57/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.57/1.50      inference(global_propositional_subsumption,
% 7.57/1.50                [status(thm)],
% 7.57/1.50                [c_495,c_22]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_500,plain,
% 7.57/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.57/1.50      | r1_tarski(k2_relat_1(X0),X2) ),
% 7.57/1.50      inference(renaming,[status(thm)],[c_499]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_564,plain,
% 7.57/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.57/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 7.57/1.50      | X4 != X1
% 7.57/1.50      | k2_relat_1(X2) != X0 ),
% 7.57/1.50      inference(resolution_lifted,[status(thm)],[c_271,c_500]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_565,plain,
% 7.57/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.57/1.50      | m1_subset_1(k2_relat_1(X0),k1_zfmisc_1(X2)) ),
% 7.57/1.50      inference(unflattening,[status(thm)],[c_564]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_22899,plain,
% 7.57/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.57/1.50      | m1_subset_1(k2_relat_1(X0),k1_zfmisc_1(X2)) = iProver_top ),
% 7.57/1.50      inference(predicate_to_equality,[status(thm)],[c_565]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_23201,plain,
% 7.57/1.50      ( m1_subset_1(k2_relat_1(sK5),k1_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3))) = iProver_top ),
% 7.57/1.50      inference(superposition,[status(thm)],[c_22906,c_22899]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_17,plain,
% 7.57/1.50      ( m1_subset_1(X0,X1)
% 7.57/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.57/1.50      | ~ r2_hidden(X0,X2) ),
% 7.57/1.50      inference(cnf_transformation,[],[f71]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_22909,plain,
% 7.57/1.50      ( m1_subset_1(X0,X1) = iProver_top
% 7.57/1.50      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 7.57/1.50      | r2_hidden(X0,X2) != iProver_top ),
% 7.57/1.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_23241,plain,
% 7.57/1.50      ( m1_subset_1(X0,k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top
% 7.57/1.50      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 7.57/1.50      inference(superposition,[status(thm)],[c_23201,c_22909]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_14,plain,
% 7.57/1.50      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 7.57/1.50      inference(cnf_transformation,[],[f68]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_22910,plain,
% 7.57/1.50      ( m1_subset_1(X0,X1) != iProver_top
% 7.57/1.50      | r2_hidden(X0,X1) = iProver_top
% 7.57/1.50      | v1_xboole_0(X1) = iProver_top ),
% 7.57/1.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_23489,plain,
% 7.57/1.50      ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top
% 7.57/1.50      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top
% 7.57/1.50      | v1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top ),
% 7.57/1.50      inference(superposition,[status(thm)],[c_23241,c_22910]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_13,negated_conjecture,
% 7.57/1.50      ( ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
% 7.57/1.50      inference(cnf_transformation,[],[f104]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_22911,plain,
% 7.57/1.50      ( v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
% 7.57/1.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_23525,plain,
% 7.57/1.50      ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top
% 7.57/1.50      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 7.57/1.50      inference(forward_subsumption_resolution,
% 7.57/1.50                [status(thm)],
% 7.57/1.50                [c_23489,c_22911]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_8,plain,
% 7.57/1.50      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
% 7.57/1.50      | X0 = X1
% 7.57/1.50      | X0 = X2
% 7.57/1.50      | X0 = X3 ),
% 7.57/1.50      inference(cnf_transformation,[],[f113]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_22914,plain,
% 7.57/1.50      ( X0 = X1
% 7.57/1.50      | X0 = X2
% 7.57/1.50      | X0 = X3
% 7.57/1.50      | r2_hidden(X0,k2_enumset1(X1,X1,X2,X3)) != iProver_top ),
% 7.57/1.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_23530,plain,
% 7.57/1.50      ( sK3 = X0 | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 7.57/1.50      inference(superposition,[status(thm)],[c_23525,c_22914]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_23566,plain,
% 7.57/1.50      ( k1_funct_1(sK5,X0) = sK3 | r2_hidden(X0,sK2) != iProver_top ),
% 7.57/1.50      inference(superposition,[status(thm)],[c_23455,c_23530]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_23594,plain,
% 7.57/1.50      ( k1_funct_1(sK5,sK4) = sK3 ),
% 7.57/1.50      inference(superposition,[status(thm)],[c_22907,c_23566]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_31,negated_conjecture,
% 7.57/1.50      ( k1_funct_1(sK5,sK4) != sK3 ),
% 7.57/1.50      inference(cnf_transformation,[],[f89]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(contradiction,plain,
% 7.57/1.50      ( $false ),
% 7.57/1.50      inference(minisat,[status(thm)],[c_23594,c_31]) ).
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.57/1.50  
% 7.57/1.50  ------                               Statistics
% 7.57/1.50  
% 7.57/1.50  ------ Selected
% 7.57/1.50  
% 7.57/1.50  total_time:                             0.642
% 7.57/1.50  
%------------------------------------------------------------------------------
