%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:06:11 EST 2020

% Result     : Theorem 2.58s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 299 expanded)
%              Number of clauses        :   58 (  86 expanded)
%              Number of leaves         :   16 (  63 expanded)
%              Depth                    :   19
%              Number of atoms          :  394 (1070 expanded)
%              Number of equality atoms :  214 ( 419 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f28,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f29,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f28])).

fof(f41,plain,
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

fof(f42,plain,
    ( k1_funct_1(sK5,sK4) != sK3
    & r2_hidden(sK4,sK2)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
    & v1_funct_2(sK5,sK2,k1_tarski(sK3))
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f29,f41])).

fof(f77,plain,(
    r2_hidden(sK4,sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f14,axiom,(
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

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f75,plain,(
    v1_funct_2(sK5,sK2,k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f42])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f79,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f59,f60])).

fof(f80,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f58,f79])).

fof(f96,plain,(
    v1_funct_2(sK5,sK2,k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(definition_unfolding,[],[f75,f80])).

fof(f76,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) ),
    inference(cnf_transformation,[],[f42])).

fof(f95,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))) ),
    inference(definition_unfolding,[],[f76,f80])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f33,plain,(
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

fof(f34,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).

fof(f45,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f87,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f45,f60])).

fof(f101,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f87])).

fof(f102,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k2_enumset1(X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f101])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f74,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f44,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f88,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f44,f60])).

fof(f103,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k2_enumset1(X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f88])).

fof(f78,plain,(
    k1_funct_1(sK5,sK4) != sK3 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_29,negated_conjecture,
    ( r2_hidden(sK4,sK2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1057,plain,
    ( r2_hidden(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK5,sK2,k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_439,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_enumset1(sK3,sK3,sK3,sK3) != X2
    | k1_relset_1(X1,X2,X0) = X1
    | sK2 != X1
    | sK5 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_31])).

cnf(c_440,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))))
    | k1_relset_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK5) = sK2
    | k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(unflattening,[status(thm)],[c_439])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_442,plain,
    ( k1_relset_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK5) = sK2
    | k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_440,c_30])).

cnf(c_1056,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1059,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2050,plain,
    ( k1_relset_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1056,c_1059])).

cnf(c_2143,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_xboole_0
    | k1_relat_1(sK5) = sK2 ),
    inference(superposition,[status(thm)],[c_442,c_2050])).

cnf(c_7,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1069,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2147,plain,
    ( k1_relat_1(sK5) = sK2
    | r2_hidden(sK3,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2143,c_1069])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_345,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_17])).

cnf(c_346,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_345])).

cnf(c_1055,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_346])).

cnf(c_2307,plain,
    ( k1_relat_1(sK5) = sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2147,c_1055])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_356,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_32])).

cnf(c_357,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK5))
    | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5))
    | ~ v1_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_356])).

cnf(c_375,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(sK5))
    | r2_hidden(k1_funct_1(sK5,X3),k2_relat_1(sK5))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_357])).

cnf(c_376,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r2_hidden(X2,k1_relat_1(sK5))
    | r2_hidden(k1_funct_1(sK5,X2),k2_relat_1(sK5)) ),
    inference(unflattening,[status(thm)],[c_375])).

cnf(c_620,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK5))
    | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_376])).

cnf(c_1054,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_620])).

cnf(c_35,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_622,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_376])).

cnf(c_648,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_622])).

cnf(c_652,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_620])).

cnf(c_621,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_376])).

cnf(c_1258,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))))
    | ~ sP1_iProver_split ),
    inference(instantiation,[status(thm)],[c_621])).

cnf(c_1259,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1258])).

cnf(c_1355,plain,
    ( r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1054,c_35,c_648,c_652,c_1259])).

cnf(c_1356,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) = iProver_top ),
    inference(renaming,[status(thm)],[c_1355])).

cnf(c_2309,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2307,c_1356])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1058,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1793,plain,
    ( k2_relset_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK5) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1056,c_1058])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1060,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2475,plain,
    ( m1_subset_1(k2_relat_1(sK5),k1_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1793,c_1060])).

cnf(c_3242,plain,
    ( m1_subset_1(k2_relat_1(sK5),k1_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2475,c_35])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1061,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3248,plain,
    ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3242,c_1061])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1068,plain,
    ( X0 = X1
    | X0 = X2
    | X0 = X3
    | r2_hidden(X0,k2_enumset1(X1,X1,X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3475,plain,
    ( sK3 = X0
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3248,c_1068])).

cnf(c_3551,plain,
    ( k1_funct_1(sK5,X0) = sK3
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2309,c_3475])).

cnf(c_4234,plain,
    ( k1_funct_1(sK5,sK4) = sK3 ),
    inference(superposition,[status(thm)],[c_1057,c_3551])).

cnf(c_28,negated_conjecture,
    ( k1_funct_1(sK5,sK4) != sK3 ),
    inference(cnf_transformation,[],[f78])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4234,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:23:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.58/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.00  
% 2.58/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.58/1.00  
% 2.58/1.00  ------  iProver source info
% 2.58/1.00  
% 2.58/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.58/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.58/1.00  git: non_committed_changes: false
% 2.58/1.00  git: last_make_outside_of_git: false
% 2.58/1.00  
% 2.58/1.00  ------ 
% 2.58/1.00  
% 2.58/1.00  ------ Input Options
% 2.58/1.00  
% 2.58/1.00  --out_options                           all
% 2.58/1.00  --tptp_safe_out                         true
% 2.58/1.00  --problem_path                          ""
% 2.58/1.00  --include_path                          ""
% 2.58/1.00  --clausifier                            res/vclausify_rel
% 2.58/1.00  --clausifier_options                    --mode clausify
% 2.58/1.00  --stdin                                 false
% 2.58/1.00  --stats_out                             all
% 2.58/1.00  
% 2.58/1.00  ------ General Options
% 2.58/1.00  
% 2.58/1.00  --fof                                   false
% 2.58/1.00  --time_out_real                         305.
% 2.58/1.00  --time_out_virtual                      -1.
% 2.58/1.00  --symbol_type_check                     false
% 2.58/1.00  --clausify_out                          false
% 2.58/1.00  --sig_cnt_out                           false
% 2.58/1.00  --trig_cnt_out                          false
% 2.58/1.00  --trig_cnt_out_tolerance                1.
% 2.58/1.00  --trig_cnt_out_sk_spl                   false
% 2.58/1.00  --abstr_cl_out                          false
% 2.58/1.00  
% 2.58/1.00  ------ Global Options
% 2.58/1.00  
% 2.58/1.00  --schedule                              default
% 2.58/1.00  --add_important_lit                     false
% 2.58/1.00  --prop_solver_per_cl                    1000
% 2.58/1.00  --min_unsat_core                        false
% 2.58/1.00  --soft_assumptions                      false
% 2.58/1.00  --soft_lemma_size                       3
% 2.58/1.00  --prop_impl_unit_size                   0
% 2.58/1.00  --prop_impl_unit                        []
% 2.58/1.00  --share_sel_clauses                     true
% 2.58/1.00  --reset_solvers                         false
% 2.58/1.00  --bc_imp_inh                            [conj_cone]
% 2.58/1.00  --conj_cone_tolerance                   3.
% 2.58/1.00  --extra_neg_conj                        none
% 2.58/1.00  --large_theory_mode                     true
% 2.58/1.00  --prolific_symb_bound                   200
% 2.58/1.00  --lt_threshold                          2000
% 2.58/1.00  --clause_weak_htbl                      true
% 2.58/1.00  --gc_record_bc_elim                     false
% 2.58/1.00  
% 2.58/1.00  ------ Preprocessing Options
% 2.58/1.00  
% 2.58/1.00  --preprocessing_flag                    true
% 2.58/1.00  --time_out_prep_mult                    0.1
% 2.58/1.00  --splitting_mode                        input
% 2.58/1.00  --splitting_grd                         true
% 2.58/1.00  --splitting_cvd                         false
% 2.58/1.00  --splitting_cvd_svl                     false
% 2.58/1.00  --splitting_nvd                         32
% 2.58/1.00  --sub_typing                            true
% 2.58/1.00  --prep_gs_sim                           true
% 2.58/1.00  --prep_unflatten                        true
% 2.58/1.00  --prep_res_sim                          true
% 2.58/1.00  --prep_upred                            true
% 2.58/1.00  --prep_sem_filter                       exhaustive
% 2.58/1.00  --prep_sem_filter_out                   false
% 2.58/1.00  --pred_elim                             true
% 2.58/1.00  --res_sim_input                         true
% 2.58/1.00  --eq_ax_congr_red                       true
% 2.58/1.00  --pure_diseq_elim                       true
% 2.58/1.00  --brand_transform                       false
% 2.58/1.00  --non_eq_to_eq                          false
% 2.58/1.00  --prep_def_merge                        true
% 2.58/1.00  --prep_def_merge_prop_impl              false
% 2.58/1.00  --prep_def_merge_mbd                    true
% 2.58/1.00  --prep_def_merge_tr_red                 false
% 2.58/1.00  --prep_def_merge_tr_cl                  false
% 2.58/1.00  --smt_preprocessing                     true
% 2.58/1.00  --smt_ac_axioms                         fast
% 2.58/1.00  --preprocessed_out                      false
% 2.58/1.00  --preprocessed_stats                    false
% 2.58/1.00  
% 2.58/1.00  ------ Abstraction refinement Options
% 2.58/1.00  
% 2.58/1.00  --abstr_ref                             []
% 2.58/1.00  --abstr_ref_prep                        false
% 2.58/1.00  --abstr_ref_until_sat                   false
% 2.58/1.00  --abstr_ref_sig_restrict                funpre
% 2.58/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.58/1.00  --abstr_ref_under                       []
% 2.58/1.00  
% 2.58/1.00  ------ SAT Options
% 2.58/1.00  
% 2.58/1.00  --sat_mode                              false
% 2.58/1.00  --sat_fm_restart_options                ""
% 2.58/1.00  --sat_gr_def                            false
% 2.58/1.00  --sat_epr_types                         true
% 2.58/1.00  --sat_non_cyclic_types                  false
% 2.58/1.00  --sat_finite_models                     false
% 2.58/1.00  --sat_fm_lemmas                         false
% 2.58/1.00  --sat_fm_prep                           false
% 2.58/1.00  --sat_fm_uc_incr                        true
% 2.58/1.00  --sat_out_model                         small
% 2.58/1.00  --sat_out_clauses                       false
% 2.58/1.00  
% 2.58/1.00  ------ QBF Options
% 2.58/1.00  
% 2.58/1.00  --qbf_mode                              false
% 2.58/1.00  --qbf_elim_univ                         false
% 2.58/1.00  --qbf_dom_inst                          none
% 2.58/1.00  --qbf_dom_pre_inst                      false
% 2.58/1.00  --qbf_sk_in                             false
% 2.58/1.00  --qbf_pred_elim                         true
% 2.58/1.00  --qbf_split                             512
% 2.58/1.00  
% 2.58/1.00  ------ BMC1 Options
% 2.58/1.00  
% 2.58/1.00  --bmc1_incremental                      false
% 2.58/1.00  --bmc1_axioms                           reachable_all
% 2.58/1.00  --bmc1_min_bound                        0
% 2.58/1.00  --bmc1_max_bound                        -1
% 2.58/1.00  --bmc1_max_bound_default                -1
% 2.58/1.00  --bmc1_symbol_reachability              true
% 2.58/1.00  --bmc1_property_lemmas                  false
% 2.58/1.00  --bmc1_k_induction                      false
% 2.58/1.00  --bmc1_non_equiv_states                 false
% 2.58/1.00  --bmc1_deadlock                         false
% 2.58/1.00  --bmc1_ucm                              false
% 2.58/1.00  --bmc1_add_unsat_core                   none
% 2.58/1.00  --bmc1_unsat_core_children              false
% 2.58/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.58/1.00  --bmc1_out_stat                         full
% 2.58/1.00  --bmc1_ground_init                      false
% 2.58/1.00  --bmc1_pre_inst_next_state              false
% 2.58/1.00  --bmc1_pre_inst_state                   false
% 2.58/1.00  --bmc1_pre_inst_reach_state             false
% 2.58/1.00  --bmc1_out_unsat_core                   false
% 2.58/1.00  --bmc1_aig_witness_out                  false
% 2.58/1.00  --bmc1_verbose                          false
% 2.58/1.00  --bmc1_dump_clauses_tptp                false
% 2.58/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.58/1.00  --bmc1_dump_file                        -
% 2.58/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.58/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.58/1.00  --bmc1_ucm_extend_mode                  1
% 2.58/1.00  --bmc1_ucm_init_mode                    2
% 2.58/1.00  --bmc1_ucm_cone_mode                    none
% 2.58/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.58/1.00  --bmc1_ucm_relax_model                  4
% 2.58/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.58/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.58/1.00  --bmc1_ucm_layered_model                none
% 2.58/1.00  --bmc1_ucm_max_lemma_size               10
% 2.58/1.00  
% 2.58/1.00  ------ AIG Options
% 2.58/1.00  
% 2.58/1.00  --aig_mode                              false
% 2.58/1.00  
% 2.58/1.00  ------ Instantiation Options
% 2.58/1.00  
% 2.58/1.00  --instantiation_flag                    true
% 2.58/1.00  --inst_sos_flag                         false
% 2.58/1.00  --inst_sos_phase                        true
% 2.58/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.58/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.58/1.00  --inst_lit_sel_side                     num_symb
% 2.58/1.00  --inst_solver_per_active                1400
% 2.58/1.00  --inst_solver_calls_frac                1.
% 2.58/1.00  --inst_passive_queue_type               priority_queues
% 2.58/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.58/1.00  --inst_passive_queues_freq              [25;2]
% 2.58/1.00  --inst_dismatching                      true
% 2.58/1.00  --inst_eager_unprocessed_to_passive     true
% 2.58/1.00  --inst_prop_sim_given                   true
% 2.58/1.00  --inst_prop_sim_new                     false
% 2.58/1.00  --inst_subs_new                         false
% 2.58/1.00  --inst_eq_res_simp                      false
% 2.58/1.00  --inst_subs_given                       false
% 2.58/1.00  --inst_orphan_elimination               true
% 2.58/1.00  --inst_learning_loop_flag               true
% 2.58/1.00  --inst_learning_start                   3000
% 2.58/1.00  --inst_learning_factor                  2
% 2.58/1.00  --inst_start_prop_sim_after_learn       3
% 2.58/1.00  --inst_sel_renew                        solver
% 2.58/1.00  --inst_lit_activity_flag                true
% 2.58/1.00  --inst_restr_to_given                   false
% 2.58/1.00  --inst_activity_threshold               500
% 2.58/1.00  --inst_out_proof                        true
% 2.58/1.00  
% 2.58/1.00  ------ Resolution Options
% 2.58/1.00  
% 2.58/1.00  --resolution_flag                       true
% 2.58/1.00  --res_lit_sel                           adaptive
% 2.58/1.00  --res_lit_sel_side                      none
% 2.58/1.00  --res_ordering                          kbo
% 2.58/1.00  --res_to_prop_solver                    active
% 2.58/1.00  --res_prop_simpl_new                    false
% 2.58/1.00  --res_prop_simpl_given                  true
% 2.58/1.00  --res_passive_queue_type                priority_queues
% 2.58/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.58/1.00  --res_passive_queues_freq               [15;5]
% 2.58/1.00  --res_forward_subs                      full
% 2.58/1.00  --res_backward_subs                     full
% 2.58/1.00  --res_forward_subs_resolution           true
% 2.58/1.00  --res_backward_subs_resolution          true
% 2.58/1.00  --res_orphan_elimination                true
% 2.58/1.00  --res_time_limit                        2.
% 2.58/1.00  --res_out_proof                         true
% 2.58/1.00  
% 2.58/1.00  ------ Superposition Options
% 2.58/1.00  
% 2.58/1.00  --superposition_flag                    true
% 2.58/1.00  --sup_passive_queue_type                priority_queues
% 2.58/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.58/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.58/1.00  --demod_completeness_check              fast
% 2.58/1.00  --demod_use_ground                      true
% 2.58/1.00  --sup_to_prop_solver                    passive
% 2.58/1.00  --sup_prop_simpl_new                    true
% 2.58/1.00  --sup_prop_simpl_given                  true
% 2.58/1.00  --sup_fun_splitting                     false
% 2.58/1.00  --sup_smt_interval                      50000
% 2.58/1.00  
% 2.58/1.00  ------ Superposition Simplification Setup
% 2.58/1.00  
% 2.58/1.00  --sup_indices_passive                   []
% 2.58/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.58/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.58/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.58/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.58/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.58/1.00  --sup_full_bw                           [BwDemod]
% 2.58/1.00  --sup_immed_triv                        [TrivRules]
% 2.58/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.58/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.58/1.00  --sup_immed_bw_main                     []
% 2.58/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.58/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.58/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.58/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.58/1.00  
% 2.58/1.00  ------ Combination Options
% 2.58/1.00  
% 2.58/1.00  --comb_res_mult                         3
% 2.58/1.00  --comb_sup_mult                         2
% 2.58/1.00  --comb_inst_mult                        10
% 2.58/1.00  
% 2.58/1.00  ------ Debug Options
% 2.58/1.00  
% 2.58/1.00  --dbg_backtrace                         false
% 2.58/1.00  --dbg_dump_prop_clauses                 false
% 2.58/1.00  --dbg_dump_prop_clauses_file            -
% 2.58/1.00  --dbg_out_stat                          false
% 2.58/1.00  ------ Parsing...
% 2.58/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.58/1.00  
% 2.58/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.58/1.00  
% 2.58/1.00  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.58/1.00  
% 2.58/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.58/1.00  ------ Proving...
% 2.58/1.00  ------ Problem Properties 
% 2.58/1.00  
% 2.58/1.00  
% 2.58/1.00  clauses                                 28
% 2.58/1.00  conjectures                             3
% 2.58/1.00  EPR                                     3
% 2.58/1.00  Horn                                    21
% 2.58/1.00  unary                                   9
% 2.58/1.00  binary                                  6
% 2.58/1.00  lits                                    65
% 2.58/1.00  lits eq                                 32
% 2.58/1.00  fd_pure                                 0
% 2.58/1.00  fd_pseudo                               0
% 2.58/1.00  fd_cond                                 0
% 2.58/1.00  fd_pseudo_cond                          7
% 2.58/1.00  AC symbols                              0
% 2.58/1.00  
% 2.58/1.00  ------ Schedule dynamic 5 is on 
% 2.58/1.00  
% 2.58/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.58/1.00  
% 2.58/1.00  
% 2.58/1.00  ------ 
% 2.58/1.00  Current options:
% 2.58/1.00  ------ 
% 2.58/1.00  
% 2.58/1.00  ------ Input Options
% 2.58/1.00  
% 2.58/1.00  --out_options                           all
% 2.58/1.00  --tptp_safe_out                         true
% 2.58/1.00  --problem_path                          ""
% 2.58/1.00  --include_path                          ""
% 2.58/1.00  --clausifier                            res/vclausify_rel
% 2.58/1.00  --clausifier_options                    --mode clausify
% 2.58/1.00  --stdin                                 false
% 2.58/1.00  --stats_out                             all
% 2.58/1.00  
% 2.58/1.00  ------ General Options
% 2.58/1.00  
% 2.58/1.00  --fof                                   false
% 2.58/1.00  --time_out_real                         305.
% 2.58/1.00  --time_out_virtual                      -1.
% 2.58/1.00  --symbol_type_check                     false
% 2.58/1.00  --clausify_out                          false
% 2.58/1.00  --sig_cnt_out                           false
% 2.58/1.00  --trig_cnt_out                          false
% 2.58/1.00  --trig_cnt_out_tolerance                1.
% 2.58/1.00  --trig_cnt_out_sk_spl                   false
% 2.58/1.00  --abstr_cl_out                          false
% 2.58/1.00  
% 2.58/1.00  ------ Global Options
% 2.58/1.00  
% 2.58/1.00  --schedule                              default
% 2.58/1.00  --add_important_lit                     false
% 2.58/1.00  --prop_solver_per_cl                    1000
% 2.58/1.00  --min_unsat_core                        false
% 2.58/1.00  --soft_assumptions                      false
% 2.58/1.00  --soft_lemma_size                       3
% 2.58/1.00  --prop_impl_unit_size                   0
% 2.58/1.00  --prop_impl_unit                        []
% 2.58/1.00  --share_sel_clauses                     true
% 2.58/1.00  --reset_solvers                         false
% 2.58/1.00  --bc_imp_inh                            [conj_cone]
% 2.58/1.00  --conj_cone_tolerance                   3.
% 2.58/1.00  --extra_neg_conj                        none
% 2.58/1.00  --large_theory_mode                     true
% 2.58/1.00  --prolific_symb_bound                   200
% 2.58/1.00  --lt_threshold                          2000
% 2.58/1.00  --clause_weak_htbl                      true
% 2.58/1.00  --gc_record_bc_elim                     false
% 2.58/1.00  
% 2.58/1.00  ------ Preprocessing Options
% 2.58/1.00  
% 2.58/1.00  --preprocessing_flag                    true
% 2.58/1.00  --time_out_prep_mult                    0.1
% 2.58/1.00  --splitting_mode                        input
% 2.58/1.00  --splitting_grd                         true
% 2.58/1.00  --splitting_cvd                         false
% 2.58/1.00  --splitting_cvd_svl                     false
% 2.58/1.00  --splitting_nvd                         32
% 2.58/1.00  --sub_typing                            true
% 2.58/1.00  --prep_gs_sim                           true
% 2.58/1.00  --prep_unflatten                        true
% 2.58/1.00  --prep_res_sim                          true
% 2.58/1.00  --prep_upred                            true
% 2.58/1.00  --prep_sem_filter                       exhaustive
% 2.58/1.00  --prep_sem_filter_out                   false
% 2.58/1.00  --pred_elim                             true
% 2.58/1.00  --res_sim_input                         true
% 2.58/1.00  --eq_ax_congr_red                       true
% 2.58/1.00  --pure_diseq_elim                       true
% 2.58/1.00  --brand_transform                       false
% 2.58/1.00  --non_eq_to_eq                          false
% 2.58/1.00  --prep_def_merge                        true
% 2.58/1.00  --prep_def_merge_prop_impl              false
% 2.58/1.00  --prep_def_merge_mbd                    true
% 2.58/1.00  --prep_def_merge_tr_red                 false
% 2.58/1.00  --prep_def_merge_tr_cl                  false
% 2.58/1.00  --smt_preprocessing                     true
% 2.58/1.00  --smt_ac_axioms                         fast
% 2.58/1.00  --preprocessed_out                      false
% 2.58/1.00  --preprocessed_stats                    false
% 2.58/1.00  
% 2.58/1.00  ------ Abstraction refinement Options
% 2.58/1.00  
% 2.58/1.00  --abstr_ref                             []
% 2.58/1.00  --abstr_ref_prep                        false
% 2.58/1.00  --abstr_ref_until_sat                   false
% 2.58/1.00  --abstr_ref_sig_restrict                funpre
% 2.58/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.58/1.00  --abstr_ref_under                       []
% 2.58/1.00  
% 2.58/1.00  ------ SAT Options
% 2.58/1.00  
% 2.58/1.00  --sat_mode                              false
% 2.58/1.00  --sat_fm_restart_options                ""
% 2.58/1.00  --sat_gr_def                            false
% 2.58/1.00  --sat_epr_types                         true
% 2.58/1.00  --sat_non_cyclic_types                  false
% 2.58/1.00  --sat_finite_models                     false
% 2.58/1.00  --sat_fm_lemmas                         false
% 2.58/1.00  --sat_fm_prep                           false
% 2.58/1.00  --sat_fm_uc_incr                        true
% 2.58/1.00  --sat_out_model                         small
% 2.58/1.00  --sat_out_clauses                       false
% 2.58/1.00  
% 2.58/1.00  ------ QBF Options
% 2.58/1.00  
% 2.58/1.00  --qbf_mode                              false
% 2.58/1.00  --qbf_elim_univ                         false
% 2.58/1.00  --qbf_dom_inst                          none
% 2.58/1.00  --qbf_dom_pre_inst                      false
% 2.58/1.00  --qbf_sk_in                             false
% 2.58/1.00  --qbf_pred_elim                         true
% 2.58/1.00  --qbf_split                             512
% 2.58/1.00  
% 2.58/1.00  ------ BMC1 Options
% 2.58/1.00  
% 2.58/1.00  --bmc1_incremental                      false
% 2.58/1.00  --bmc1_axioms                           reachable_all
% 2.58/1.00  --bmc1_min_bound                        0
% 2.58/1.00  --bmc1_max_bound                        -1
% 2.58/1.00  --bmc1_max_bound_default                -1
% 2.58/1.00  --bmc1_symbol_reachability              true
% 2.58/1.00  --bmc1_property_lemmas                  false
% 2.58/1.00  --bmc1_k_induction                      false
% 2.58/1.00  --bmc1_non_equiv_states                 false
% 2.58/1.00  --bmc1_deadlock                         false
% 2.58/1.00  --bmc1_ucm                              false
% 2.58/1.00  --bmc1_add_unsat_core                   none
% 2.58/1.00  --bmc1_unsat_core_children              false
% 2.58/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.58/1.00  --bmc1_out_stat                         full
% 2.58/1.00  --bmc1_ground_init                      false
% 2.58/1.00  --bmc1_pre_inst_next_state              false
% 2.58/1.00  --bmc1_pre_inst_state                   false
% 2.58/1.00  --bmc1_pre_inst_reach_state             false
% 2.58/1.00  --bmc1_out_unsat_core                   false
% 2.58/1.00  --bmc1_aig_witness_out                  false
% 2.58/1.00  --bmc1_verbose                          false
% 2.58/1.00  --bmc1_dump_clauses_tptp                false
% 2.58/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.58/1.00  --bmc1_dump_file                        -
% 2.58/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.58/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.58/1.00  --bmc1_ucm_extend_mode                  1
% 2.58/1.00  --bmc1_ucm_init_mode                    2
% 2.58/1.00  --bmc1_ucm_cone_mode                    none
% 2.58/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.58/1.00  --bmc1_ucm_relax_model                  4
% 2.58/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.58/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.58/1.00  --bmc1_ucm_layered_model                none
% 2.58/1.00  --bmc1_ucm_max_lemma_size               10
% 2.58/1.00  
% 2.58/1.00  ------ AIG Options
% 2.58/1.00  
% 2.58/1.00  --aig_mode                              false
% 2.58/1.00  
% 2.58/1.00  ------ Instantiation Options
% 2.58/1.00  
% 2.58/1.00  --instantiation_flag                    true
% 2.58/1.00  --inst_sos_flag                         false
% 2.58/1.00  --inst_sos_phase                        true
% 2.58/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.58/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.58/1.00  --inst_lit_sel_side                     none
% 2.58/1.00  --inst_solver_per_active                1400
% 2.58/1.00  --inst_solver_calls_frac                1.
% 2.58/1.00  --inst_passive_queue_type               priority_queues
% 2.58/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.58/1.00  --inst_passive_queues_freq              [25;2]
% 2.58/1.00  --inst_dismatching                      true
% 2.58/1.00  --inst_eager_unprocessed_to_passive     true
% 2.58/1.00  --inst_prop_sim_given                   true
% 2.58/1.00  --inst_prop_sim_new                     false
% 2.58/1.00  --inst_subs_new                         false
% 2.58/1.00  --inst_eq_res_simp                      false
% 2.58/1.00  --inst_subs_given                       false
% 2.58/1.00  --inst_orphan_elimination               true
% 2.58/1.00  --inst_learning_loop_flag               true
% 2.58/1.00  --inst_learning_start                   3000
% 2.58/1.00  --inst_learning_factor                  2
% 2.58/1.00  --inst_start_prop_sim_after_learn       3
% 2.58/1.00  --inst_sel_renew                        solver
% 2.58/1.00  --inst_lit_activity_flag                true
% 2.58/1.00  --inst_restr_to_given                   false
% 2.58/1.00  --inst_activity_threshold               500
% 2.58/1.00  --inst_out_proof                        true
% 2.58/1.00  
% 2.58/1.00  ------ Resolution Options
% 2.58/1.00  
% 2.58/1.00  --resolution_flag                       false
% 2.58/1.00  --res_lit_sel                           adaptive
% 2.58/1.00  --res_lit_sel_side                      none
% 2.58/1.00  --res_ordering                          kbo
% 2.58/1.00  --res_to_prop_solver                    active
% 2.58/1.00  --res_prop_simpl_new                    false
% 2.58/1.00  --res_prop_simpl_given                  true
% 2.58/1.00  --res_passive_queue_type                priority_queues
% 2.58/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.58/1.00  --res_passive_queues_freq               [15;5]
% 2.58/1.00  --res_forward_subs                      full
% 2.58/1.00  --res_backward_subs                     full
% 2.58/1.00  --res_forward_subs_resolution           true
% 2.58/1.00  --res_backward_subs_resolution          true
% 2.58/1.00  --res_orphan_elimination                true
% 2.58/1.00  --res_time_limit                        2.
% 2.58/1.00  --res_out_proof                         true
% 2.58/1.00  
% 2.58/1.00  ------ Superposition Options
% 2.58/1.00  
% 2.58/1.00  --superposition_flag                    true
% 2.58/1.00  --sup_passive_queue_type                priority_queues
% 2.58/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.58/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.58/1.00  --demod_completeness_check              fast
% 2.58/1.00  --demod_use_ground                      true
% 2.58/1.00  --sup_to_prop_solver                    passive
% 2.58/1.00  --sup_prop_simpl_new                    true
% 2.58/1.00  --sup_prop_simpl_given                  true
% 2.58/1.00  --sup_fun_splitting                     false
% 2.58/1.00  --sup_smt_interval                      50000
% 2.58/1.00  
% 2.58/1.00  ------ Superposition Simplification Setup
% 2.58/1.00  
% 2.58/1.00  --sup_indices_passive                   []
% 2.58/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.58/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.58/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.58/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.58/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.58/1.00  --sup_full_bw                           [BwDemod]
% 2.58/1.00  --sup_immed_triv                        [TrivRules]
% 2.58/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.58/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.58/1.00  --sup_immed_bw_main                     []
% 2.58/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.58/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.58/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.58/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.58/1.00  
% 2.58/1.00  ------ Combination Options
% 2.58/1.00  
% 2.58/1.00  --comb_res_mult                         3
% 2.58/1.00  --comb_sup_mult                         2
% 2.58/1.00  --comb_inst_mult                        10
% 2.58/1.00  
% 2.58/1.00  ------ Debug Options
% 2.58/1.00  
% 2.58/1.00  --dbg_backtrace                         false
% 2.58/1.00  --dbg_dump_prop_clauses                 false
% 2.58/1.00  --dbg_dump_prop_clauses_file            -
% 2.58/1.00  --dbg_out_stat                          false
% 2.58/1.00  
% 2.58/1.00  
% 2.58/1.00  
% 2.58/1.00  
% 2.58/1.00  ------ Proving...
% 2.58/1.00  
% 2.58/1.00  
% 2.58/1.00  % SZS status Theorem for theBenchmark.p
% 2.58/1.00  
% 2.58/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.58/1.00  
% 2.58/1.00  fof(f15,conjecture,(
% 2.58/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 2.58/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f16,negated_conjecture,(
% 2.58/1.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 2.58/1.00    inference(negated_conjecture,[],[f15])).
% 2.58/1.00  
% 2.58/1.00  fof(f28,plain,(
% 2.58/1.00    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 2.58/1.00    inference(ennf_transformation,[],[f16])).
% 2.58/1.00  
% 2.58/1.00  fof(f29,plain,(
% 2.58/1.00    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 2.58/1.00    inference(flattening,[],[f28])).
% 2.58/1.00  
% 2.58/1.00  fof(f41,plain,(
% 2.58/1.00    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (k1_funct_1(sK5,sK4) != sK3 & r2_hidden(sK4,sK2) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) & v1_funct_2(sK5,sK2,k1_tarski(sK3)) & v1_funct_1(sK5))),
% 2.58/1.00    introduced(choice_axiom,[])).
% 2.58/1.00  
% 2.58/1.00  fof(f42,plain,(
% 2.58/1.00    k1_funct_1(sK5,sK4) != sK3 & r2_hidden(sK4,sK2) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) & v1_funct_2(sK5,sK2,k1_tarski(sK3)) & v1_funct_1(sK5)),
% 2.58/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f29,f41])).
% 2.58/1.00  
% 2.58/1.00  fof(f77,plain,(
% 2.58/1.00    r2_hidden(sK4,sK2)),
% 2.58/1.00    inference(cnf_transformation,[],[f42])).
% 2.58/1.00  
% 2.58/1.00  fof(f14,axiom,(
% 2.58/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.58/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f26,plain,(
% 2.58/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.58/1.00    inference(ennf_transformation,[],[f14])).
% 2.58/1.00  
% 2.58/1.00  fof(f27,plain,(
% 2.58/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.58/1.00    inference(flattening,[],[f26])).
% 2.58/1.00  
% 2.58/1.00  fof(f40,plain,(
% 2.58/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.58/1.00    inference(nnf_transformation,[],[f27])).
% 2.58/1.00  
% 2.58/1.00  fof(f68,plain,(
% 2.58/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.58/1.00    inference(cnf_transformation,[],[f40])).
% 2.58/1.00  
% 2.58/1.00  fof(f75,plain,(
% 2.58/1.00    v1_funct_2(sK5,sK2,k1_tarski(sK3))),
% 2.58/1.00    inference(cnf_transformation,[],[f42])).
% 2.58/1.00  
% 2.58/1.00  fof(f4,axiom,(
% 2.58/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.58/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f58,plain,(
% 2.58/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.58/1.00    inference(cnf_transformation,[],[f4])).
% 2.58/1.00  
% 2.58/1.00  fof(f5,axiom,(
% 2.58/1.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.58/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f59,plain,(
% 2.58/1.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.58/1.00    inference(cnf_transformation,[],[f5])).
% 2.58/1.00  
% 2.58/1.00  fof(f6,axiom,(
% 2.58/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.58/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f60,plain,(
% 2.58/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.58/1.00    inference(cnf_transformation,[],[f6])).
% 2.58/1.00  
% 2.58/1.00  fof(f79,plain,(
% 2.58/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.58/1.00    inference(definition_unfolding,[],[f59,f60])).
% 2.58/1.00  
% 2.58/1.00  fof(f80,plain,(
% 2.58/1.00    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.58/1.00    inference(definition_unfolding,[],[f58,f79])).
% 2.58/1.00  
% 2.58/1.00  fof(f96,plain,(
% 2.58/1.00    v1_funct_2(sK5,sK2,k2_enumset1(sK3,sK3,sK3,sK3))),
% 2.58/1.00    inference(definition_unfolding,[],[f75,f80])).
% 2.58/1.00  
% 2.58/1.00  fof(f76,plain,(
% 2.58/1.00    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))),
% 2.58/1.00    inference(cnf_transformation,[],[f42])).
% 2.58/1.00  
% 2.58/1.00  fof(f95,plain,(
% 2.58/1.00    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))))),
% 2.58/1.00    inference(definition_unfolding,[],[f76,f80])).
% 2.58/1.00  
% 2.58/1.00  fof(f12,axiom,(
% 2.58/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.58/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f24,plain,(
% 2.58/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.58/1.00    inference(ennf_transformation,[],[f12])).
% 2.58/1.00  
% 2.58/1.00  fof(f66,plain,(
% 2.58/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.58/1.00    inference(cnf_transformation,[],[f24])).
% 2.58/1.00  
% 2.58/1.00  fof(f2,axiom,(
% 2.58/1.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 2.58/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f17,plain,(
% 2.58/1.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 2.58/1.00    inference(ennf_transformation,[],[f2])).
% 2.58/1.00  
% 2.58/1.00  fof(f30,plain,(
% 2.58/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.58/1.00    inference(nnf_transformation,[],[f17])).
% 2.58/1.00  
% 2.58/1.00  fof(f31,plain,(
% 2.58/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.58/1.00    inference(flattening,[],[f30])).
% 2.58/1.00  
% 2.58/1.00  fof(f32,plain,(
% 2.58/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.58/1.00    inference(rectify,[],[f31])).
% 2.58/1.00  
% 2.58/1.00  fof(f33,plain,(
% 2.58/1.00    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 2.58/1.00    introduced(choice_axiom,[])).
% 2.58/1.00  
% 2.58/1.00  fof(f34,plain,(
% 2.58/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.58/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).
% 2.58/1.00  
% 2.58/1.00  fof(f45,plain,(
% 2.58/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 2.58/1.00    inference(cnf_transformation,[],[f34])).
% 2.58/1.00  
% 2.58/1.00  fof(f87,plain,(
% 2.58/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 2.58/1.00    inference(definition_unfolding,[],[f45,f60])).
% 2.58/1.00  
% 2.58/1.00  fof(f101,plain,(
% 2.58/1.00    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X5,X5,X1,X2) != X3) )),
% 2.58/1.00    inference(equality_resolution,[],[f87])).
% 2.58/1.00  
% 2.58/1.00  fof(f102,plain,(
% 2.58/1.00    ( ! [X2,X5,X1] : (r2_hidden(X5,k2_enumset1(X5,X5,X1,X2))) )),
% 2.58/1.00    inference(equality_resolution,[],[f101])).
% 2.58/1.00  
% 2.58/1.00  fof(f1,axiom,(
% 2.58/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.58/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f43,plain,(
% 2.58/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.58/1.00    inference(cnf_transformation,[],[f1])).
% 2.58/1.00  
% 2.58/1.00  fof(f9,axiom,(
% 2.58/1.00    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.58/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f21,plain,(
% 2.58/1.00    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.58/1.00    inference(ennf_transformation,[],[f9])).
% 2.58/1.00  
% 2.58/1.00  fof(f63,plain,(
% 2.58/1.00    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.58/1.00    inference(cnf_transformation,[],[f21])).
% 2.58/1.00  
% 2.58/1.00  fof(f10,axiom,(
% 2.58/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.58/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f22,plain,(
% 2.58/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.58/1.00    inference(ennf_transformation,[],[f10])).
% 2.58/1.00  
% 2.58/1.00  fof(f64,plain,(
% 2.58/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.58/1.00    inference(cnf_transformation,[],[f22])).
% 2.58/1.00  
% 2.58/1.00  fof(f8,axiom,(
% 2.58/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 2.58/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f19,plain,(
% 2.58/1.00    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.58/1.00    inference(ennf_transformation,[],[f8])).
% 2.58/1.00  
% 2.58/1.00  fof(f20,plain,(
% 2.58/1.00    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.58/1.00    inference(flattening,[],[f19])).
% 2.58/1.00  
% 2.58/1.00  fof(f62,plain,(
% 2.58/1.00    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.58/1.00    inference(cnf_transformation,[],[f20])).
% 2.58/1.00  
% 2.58/1.00  fof(f74,plain,(
% 2.58/1.00    v1_funct_1(sK5)),
% 2.58/1.00    inference(cnf_transformation,[],[f42])).
% 2.58/1.00  
% 2.58/1.00  fof(f13,axiom,(
% 2.58/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.58/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f25,plain,(
% 2.58/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.58/1.00    inference(ennf_transformation,[],[f13])).
% 2.58/1.00  
% 2.58/1.00  fof(f67,plain,(
% 2.58/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.58/1.00    inference(cnf_transformation,[],[f25])).
% 2.58/1.00  
% 2.58/1.00  fof(f11,axiom,(
% 2.58/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 2.58/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f23,plain,(
% 2.58/1.00    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.58/1.00    inference(ennf_transformation,[],[f11])).
% 2.58/1.00  
% 2.58/1.00  fof(f65,plain,(
% 2.58/1.00    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.58/1.00    inference(cnf_transformation,[],[f23])).
% 2.58/1.00  
% 2.58/1.00  fof(f7,axiom,(
% 2.58/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.58/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f18,plain,(
% 2.58/1.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.58/1.00    inference(ennf_transformation,[],[f7])).
% 2.58/1.00  
% 2.58/1.00  fof(f61,plain,(
% 2.58/1.00    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.58/1.00    inference(cnf_transformation,[],[f18])).
% 2.58/1.00  
% 2.58/1.00  fof(f44,plain,(
% 2.58/1.00    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 2.58/1.00    inference(cnf_transformation,[],[f34])).
% 2.58/1.00  
% 2.58/1.00  fof(f88,plain,(
% 2.58/1.00    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 2.58/1.00    inference(definition_unfolding,[],[f44,f60])).
% 2.58/1.00  
% 2.58/1.00  fof(f103,plain,(
% 2.58/1.00    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k2_enumset1(X0,X0,X1,X2))) )),
% 2.58/1.00    inference(equality_resolution,[],[f88])).
% 2.58/1.00  
% 2.58/1.00  fof(f78,plain,(
% 2.58/1.00    k1_funct_1(sK5,sK4) != sK3),
% 2.58/1.00    inference(cnf_transformation,[],[f42])).
% 2.58/1.00  
% 2.58/1.00  cnf(c_29,negated_conjecture,
% 2.58/1.00      ( r2_hidden(sK4,sK2) ),
% 2.58/1.00      inference(cnf_transformation,[],[f77]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1057,plain,
% 2.58/1.00      ( r2_hidden(sK4,sK2) = iProver_top ),
% 2.58/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_27,plain,
% 2.58/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.58/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.58/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.58/1.00      | k1_xboole_0 = X2 ),
% 2.58/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_31,negated_conjecture,
% 2.58/1.00      ( v1_funct_2(sK5,sK2,k2_enumset1(sK3,sK3,sK3,sK3)) ),
% 2.58/1.00      inference(cnf_transformation,[],[f96]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_439,plain,
% 2.58/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.58/1.00      | k2_enumset1(sK3,sK3,sK3,sK3) != X2
% 2.58/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.58/1.00      | sK2 != X1
% 2.58/1.00      | sK5 != X0
% 2.58/1.00      | k1_xboole_0 = X2 ),
% 2.58/1.00      inference(resolution_lifted,[status(thm)],[c_27,c_31]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_440,plain,
% 2.58/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))))
% 2.58/1.00      | k1_relset_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK5) = sK2
% 2.58/1.00      | k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 2.58/1.00      inference(unflattening,[status(thm)],[c_439]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_30,negated_conjecture,
% 2.58/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))) ),
% 2.58/1.00      inference(cnf_transformation,[],[f95]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_442,plain,
% 2.58/1.00      ( k1_relset_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK5) = sK2
% 2.58/1.00      | k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 2.58/1.00      inference(global_propositional_subsumption,
% 2.58/1.00                [status(thm)],
% 2.58/1.00                [c_440,c_30]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1056,plain,
% 2.58/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))) = iProver_top ),
% 2.58/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_20,plain,
% 2.58/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.58/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.58/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1059,plain,
% 2.58/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.58/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.58/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_2050,plain,
% 2.58/1.00      ( k1_relset_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK5) = k1_relat_1(sK5) ),
% 2.58/1.00      inference(superposition,[status(thm)],[c_1056,c_1059]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_2143,plain,
% 2.58/1.00      ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_xboole_0
% 2.58/1.00      | k1_relat_1(sK5) = sK2 ),
% 2.58/1.00      inference(superposition,[status(thm)],[c_442,c_2050]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_7,plain,
% 2.58/1.00      ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
% 2.58/1.00      inference(cnf_transformation,[],[f102]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1069,plain,
% 2.58/1.00      ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) = iProver_top ),
% 2.58/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_2147,plain,
% 2.58/1.00      ( k1_relat_1(sK5) = sK2
% 2.58/1.00      | r2_hidden(sK3,k1_xboole_0) = iProver_top ),
% 2.58/1.00      inference(superposition,[status(thm)],[c_2143,c_1069]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_0,plain,
% 2.58/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 2.58/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_17,plain,
% 2.58/1.00      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 2.58/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_345,plain,
% 2.58/1.00      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 2.58/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_17]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_346,plain,
% 2.58/1.00      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 2.58/1.00      inference(unflattening,[status(thm)],[c_345]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1055,plain,
% 2.58/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.58/1.00      inference(predicate_to_equality,[status(thm)],[c_346]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_2307,plain,
% 2.58/1.00      ( k1_relat_1(sK5) = sK2 ),
% 2.58/1.00      inference(forward_subsumption_resolution,
% 2.58/1.00                [status(thm)],
% 2.58/1.00                [c_2147,c_1055]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_18,plain,
% 2.58/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.58/1.00      | v1_relat_1(X0) ),
% 2.58/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_16,plain,
% 2.58/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.58/1.00      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 2.58/1.00      | ~ v1_relat_1(X1)
% 2.58/1.00      | ~ v1_funct_1(X1) ),
% 2.58/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_32,negated_conjecture,
% 2.58/1.00      ( v1_funct_1(sK5) ),
% 2.58/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_356,plain,
% 2.58/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.58/1.00      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 2.58/1.00      | ~ v1_relat_1(X1)
% 2.58/1.00      | sK5 != X1 ),
% 2.58/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_32]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_357,plain,
% 2.58/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK5))
% 2.58/1.00      | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5))
% 2.58/1.00      | ~ v1_relat_1(sK5) ),
% 2.58/1.00      inference(unflattening,[status(thm)],[c_356]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_375,plain,
% 2.58/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.58/1.00      | ~ r2_hidden(X3,k1_relat_1(sK5))
% 2.58/1.00      | r2_hidden(k1_funct_1(sK5,X3),k2_relat_1(sK5))
% 2.58/1.00      | sK5 != X0 ),
% 2.58/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_357]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_376,plain,
% 2.58/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.58/1.00      | ~ r2_hidden(X2,k1_relat_1(sK5))
% 2.58/1.00      | r2_hidden(k1_funct_1(sK5,X2),k2_relat_1(sK5)) ),
% 2.58/1.00      inference(unflattening,[status(thm)],[c_375]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_620,plain,
% 2.58/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK5))
% 2.58/1.00      | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5))
% 2.58/1.00      | ~ sP0_iProver_split ),
% 2.58/1.00      inference(splitting,
% 2.58/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.58/1.00                [c_376]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1054,plain,
% 2.58/1.00      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 2.58/1.00      | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) = iProver_top
% 2.58/1.00      | sP0_iProver_split != iProver_top ),
% 2.58/1.00      inference(predicate_to_equality,[status(thm)],[c_620]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_35,plain,
% 2.58/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))) = iProver_top ),
% 2.58/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_622,plain,
% 2.58/1.00      ( sP1_iProver_split | sP0_iProver_split ),
% 2.58/1.00      inference(splitting,
% 2.58/1.00                [splitting(split),new_symbols(definition,[])],
% 2.58/1.00                [c_376]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_648,plain,
% 2.58/1.00      ( sP1_iProver_split = iProver_top
% 2.58/1.00      | sP0_iProver_split = iProver_top ),
% 2.58/1.00      inference(predicate_to_equality,[status(thm)],[c_622]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_652,plain,
% 2.58/1.00      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 2.58/1.00      | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) = iProver_top
% 2.58/1.00      | sP0_iProver_split != iProver_top ),
% 2.58/1.00      inference(predicate_to_equality,[status(thm)],[c_620]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_621,plain,
% 2.58/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.58/1.00      | ~ sP1_iProver_split ),
% 2.58/1.00      inference(splitting,
% 2.58/1.00                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 2.58/1.00                [c_376]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1258,plain,
% 2.58/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))))
% 2.58/1.00      | ~ sP1_iProver_split ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_621]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1259,plain,
% 2.58/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))) != iProver_top
% 2.58/1.00      | sP1_iProver_split != iProver_top ),
% 2.58/1.00      inference(predicate_to_equality,[status(thm)],[c_1258]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1355,plain,
% 2.58/1.00      ( r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) = iProver_top
% 2.58/1.00      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 2.58/1.00      inference(global_propositional_subsumption,
% 2.58/1.00                [status(thm)],
% 2.58/1.00                [c_1054,c_35,c_648,c_652,c_1259]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1356,plain,
% 2.58/1.00      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 2.58/1.00      | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) = iProver_top ),
% 2.58/1.00      inference(renaming,[status(thm)],[c_1355]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_2309,plain,
% 2.58/1.00      ( r2_hidden(X0,sK2) != iProver_top
% 2.58/1.00      | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) = iProver_top ),
% 2.58/1.00      inference(demodulation,[status(thm)],[c_2307,c_1356]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_21,plain,
% 2.58/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.58/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.58/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1058,plain,
% 2.58/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.58/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.58/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1793,plain,
% 2.58/1.00      ( k2_relset_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK5) = k2_relat_1(sK5) ),
% 2.58/1.00      inference(superposition,[status(thm)],[c_1056,c_1058]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_19,plain,
% 2.58/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.58/1.00      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 2.58/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1060,plain,
% 2.58/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.58/1.00      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 2.58/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_2475,plain,
% 2.58/1.00      ( m1_subset_1(k2_relat_1(sK5),k1_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3))) = iProver_top
% 2.58/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))) != iProver_top ),
% 2.58/1.00      inference(superposition,[status(thm)],[c_1793,c_1060]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_3242,plain,
% 2.58/1.00      ( m1_subset_1(k2_relat_1(sK5),k1_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3))) = iProver_top ),
% 2.58/1.00      inference(global_propositional_subsumption,
% 2.58/1.00                [status(thm)],
% 2.58/1.00                [c_2475,c_35]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_15,plain,
% 2.58/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.58/1.00      | ~ r2_hidden(X2,X0)
% 2.58/1.00      | r2_hidden(X2,X1) ),
% 2.58/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1061,plain,
% 2.58/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.58/1.00      | r2_hidden(X2,X0) != iProver_top
% 2.58/1.00      | r2_hidden(X2,X1) = iProver_top ),
% 2.58/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_3248,plain,
% 2.58/1.00      ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top
% 2.58/1.00      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 2.58/1.00      inference(superposition,[status(thm)],[c_3242,c_1061]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_8,plain,
% 2.58/1.00      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
% 2.58/1.00      | X0 = X1
% 2.58/1.00      | X0 = X2
% 2.58/1.00      | X0 = X3 ),
% 2.58/1.00      inference(cnf_transformation,[],[f103]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1068,plain,
% 2.58/1.00      ( X0 = X1
% 2.58/1.00      | X0 = X2
% 2.58/1.00      | X0 = X3
% 2.58/1.00      | r2_hidden(X0,k2_enumset1(X1,X1,X2,X3)) != iProver_top ),
% 2.58/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_3475,plain,
% 2.58/1.00      ( sK3 = X0 | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 2.58/1.00      inference(superposition,[status(thm)],[c_3248,c_1068]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_3551,plain,
% 2.58/1.00      ( k1_funct_1(sK5,X0) = sK3 | r2_hidden(X0,sK2) != iProver_top ),
% 2.58/1.00      inference(superposition,[status(thm)],[c_2309,c_3475]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_4234,plain,
% 2.58/1.00      ( k1_funct_1(sK5,sK4) = sK3 ),
% 2.58/1.00      inference(superposition,[status(thm)],[c_1057,c_3551]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_28,negated_conjecture,
% 2.58/1.00      ( k1_funct_1(sK5,sK4) != sK3 ),
% 2.58/1.00      inference(cnf_transformation,[],[f78]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(contradiction,plain,
% 2.58/1.00      ( $false ),
% 2.58/1.00      inference(minisat,[status(thm)],[c_4234,c_28]) ).
% 2.58/1.00  
% 2.58/1.00  
% 2.58/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.58/1.00  
% 2.58/1.00  ------                               Statistics
% 2.58/1.00  
% 2.58/1.00  ------ General
% 2.58/1.00  
% 2.58/1.00  abstr_ref_over_cycles:                  0
% 2.58/1.00  abstr_ref_under_cycles:                 0
% 2.58/1.00  gc_basic_clause_elim:                   0
% 2.58/1.00  forced_gc_time:                         0
% 2.58/1.00  parsing_time:                           0.011
% 2.58/1.00  unif_index_cands_time:                  0.
% 2.58/1.00  unif_index_add_time:                    0.
% 2.58/1.00  orderings_time:                         0.
% 2.58/1.00  out_proof_time:                         0.012
% 2.58/1.00  total_time:                             0.153
% 2.58/1.00  num_of_symbols:                         54
% 2.58/1.00  num_of_terms:                           5197
% 2.58/1.00  
% 2.58/1.00  ------ Preprocessing
% 2.58/1.00  
% 2.58/1.00  num_of_splits:                          2
% 2.58/1.00  num_of_split_atoms:                     2
% 2.58/1.00  num_of_reused_defs:                     0
% 2.58/1.00  num_eq_ax_congr_red:                    36
% 2.58/1.00  num_of_sem_filtered_clauses:            1
% 2.58/1.00  num_of_subtypes:                        0
% 2.58/1.00  monotx_restored_types:                  0
% 2.58/1.00  sat_num_of_epr_types:                   0
% 2.58/1.00  sat_num_of_non_cyclic_types:            0
% 2.58/1.00  sat_guarded_non_collapsed_types:        0
% 2.58/1.00  num_pure_diseq_elim:                    0
% 2.58/1.00  simp_replaced_by:                       0
% 2.58/1.00  res_preprocessed:                       138
% 2.58/1.00  prep_upred:                             0
% 2.58/1.00  prep_unflattend:                        31
% 2.58/1.00  smt_new_axioms:                         0
% 2.58/1.00  pred_elim_cands:                        2
% 2.58/1.00  pred_elim:                              4
% 2.58/1.00  pred_elim_cl:                           7
% 2.58/1.00  pred_elim_cycles:                       6
% 2.58/1.00  merged_defs:                            0
% 2.58/1.00  merged_defs_ncl:                        0
% 2.58/1.00  bin_hyper_res:                          0
% 2.58/1.00  prep_cycles:                            4
% 2.58/1.00  pred_elim_time:                         0.004
% 2.58/1.00  splitting_time:                         0.
% 2.58/1.00  sem_filter_time:                        0.
% 2.58/1.00  monotx_time:                            0.
% 2.58/1.00  subtype_inf_time:                       0.
% 2.58/1.00  
% 2.58/1.00  ------ Problem properties
% 2.58/1.00  
% 2.58/1.00  clauses:                                28
% 2.58/1.00  conjectures:                            3
% 2.58/1.00  epr:                                    3
% 2.58/1.00  horn:                                   21
% 2.58/1.00  ground:                                 7
% 2.58/1.00  unary:                                  9
% 2.58/1.00  binary:                                 6
% 2.58/1.00  lits:                                   65
% 2.58/1.00  lits_eq:                                32
% 2.58/1.00  fd_pure:                                0
% 2.58/1.00  fd_pseudo:                              0
% 2.58/1.00  fd_cond:                                0
% 2.58/1.00  fd_pseudo_cond:                         7
% 2.58/1.00  ac_symbols:                             0
% 2.58/1.00  
% 2.58/1.00  ------ Propositional Solver
% 2.58/1.00  
% 2.58/1.00  prop_solver_calls:                      26
% 2.58/1.00  prop_fast_solver_calls:                 786
% 2.58/1.00  smt_solver_calls:                       0
% 2.58/1.00  smt_fast_solver_calls:                  0
% 2.58/1.00  prop_num_of_clauses:                    1551
% 2.58/1.00  prop_preprocess_simplified:             6335
% 2.58/1.00  prop_fo_subsumed:                       7
% 2.58/1.00  prop_solver_time:                       0.
% 2.58/1.00  smt_solver_time:                        0.
% 2.58/1.00  smt_fast_solver_time:                   0.
% 2.58/1.00  prop_fast_solver_time:                  0.
% 2.58/1.00  prop_unsat_core_time:                   0.
% 2.58/1.00  
% 2.58/1.00  ------ QBF
% 2.58/1.00  
% 2.58/1.00  qbf_q_res:                              0
% 2.58/1.00  qbf_num_tautologies:                    0
% 2.58/1.00  qbf_prep_cycles:                        0
% 2.58/1.00  
% 2.58/1.00  ------ BMC1
% 2.58/1.00  
% 2.58/1.00  bmc1_current_bound:                     -1
% 2.58/1.00  bmc1_last_solved_bound:                 -1
% 2.58/1.00  bmc1_unsat_core_size:                   -1
% 2.58/1.00  bmc1_unsat_core_parents_size:           -1
% 2.58/1.00  bmc1_merge_next_fun:                    0
% 2.58/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.58/1.00  
% 2.58/1.00  ------ Instantiation
% 2.58/1.00  
% 2.58/1.00  inst_num_of_clauses:                    467
% 2.58/1.00  inst_num_in_passive:                    187
% 2.58/1.00  inst_num_in_active:                     180
% 2.58/1.00  inst_num_in_unprocessed:                100
% 2.58/1.00  inst_num_of_loops:                      190
% 2.58/1.00  inst_num_of_learning_restarts:          0
% 2.58/1.00  inst_num_moves_active_passive:          9
% 2.58/1.00  inst_lit_activity:                      0
% 2.58/1.00  inst_lit_activity_moves:                0
% 2.58/1.00  inst_num_tautologies:                   0
% 2.58/1.00  inst_num_prop_implied:                  0
% 2.58/1.00  inst_num_existing_simplified:           0
% 2.58/1.00  inst_num_eq_res_simplified:             0
% 2.58/1.00  inst_num_child_elim:                    0
% 2.58/1.00  inst_num_of_dismatching_blockings:      291
% 2.58/1.00  inst_num_of_non_proper_insts:           307
% 2.58/1.00  inst_num_of_duplicates:                 0
% 2.58/1.00  inst_inst_num_from_inst_to_res:         0
% 2.58/1.00  inst_dismatching_checking_time:         0.
% 2.58/1.00  
% 2.58/1.00  ------ Resolution
% 2.58/1.00  
% 2.58/1.00  res_num_of_clauses:                     0
% 2.58/1.00  res_num_in_passive:                     0
% 2.58/1.00  res_num_in_active:                      0
% 2.58/1.00  res_num_of_loops:                       142
% 2.58/1.00  res_forward_subset_subsumed:            192
% 2.58/1.00  res_backward_subset_subsumed:           0
% 2.58/1.00  res_forward_subsumed:                   0
% 2.58/1.00  res_backward_subsumed:                  0
% 2.58/1.00  res_forward_subsumption_resolution:     0
% 2.58/1.00  res_backward_subsumption_resolution:    0
% 2.58/1.00  res_clause_to_clause_subsumption:       122
% 2.58/1.00  res_orphan_elimination:                 0
% 2.58/1.00  res_tautology_del:                      22
% 2.58/1.00  res_num_eq_res_simplified:              0
% 2.58/1.00  res_num_sel_changes:                    0
% 2.58/1.00  res_moves_from_active_to_pass:          0
% 2.58/1.00  
% 2.58/1.00  ------ Superposition
% 2.58/1.00  
% 2.58/1.00  sup_time_total:                         0.
% 2.58/1.00  sup_time_generating:                    0.
% 2.58/1.00  sup_time_sim_full:                      0.
% 2.58/1.00  sup_time_sim_immed:                     0.
% 2.58/1.00  
% 2.58/1.00  sup_num_of_clauses:                     43
% 2.58/1.00  sup_num_in_active:                      33
% 2.58/1.00  sup_num_in_passive:                     10
% 2.58/1.00  sup_num_of_loops:                       36
% 2.58/1.00  sup_fw_superposition:                   21
% 2.58/1.00  sup_bw_superposition:                   20
% 2.58/1.00  sup_immediate_simplified:               7
% 2.58/1.00  sup_given_eliminated:                   0
% 2.58/1.00  comparisons_done:                       0
% 2.58/1.00  comparisons_avoided:                    7
% 2.58/1.00  
% 2.58/1.00  ------ Simplifications
% 2.58/1.00  
% 2.58/1.00  
% 2.58/1.00  sim_fw_subset_subsumed:                 5
% 2.58/1.00  sim_bw_subset_subsumed:                 3
% 2.58/1.00  sim_fw_subsumed:                        1
% 2.58/1.00  sim_bw_subsumed:                        2
% 2.58/1.00  sim_fw_subsumption_res:                 2
% 2.58/1.00  sim_bw_subsumption_res:                 0
% 2.58/1.00  sim_tautology_del:                      0
% 2.58/1.00  sim_eq_tautology_del:                   2
% 2.58/1.00  sim_eq_res_simp:                        0
% 2.58/1.00  sim_fw_demodulated:                     0
% 2.58/1.00  sim_bw_demodulated:                     2
% 2.58/1.00  sim_light_normalised:                   0
% 2.58/1.00  sim_joinable_taut:                      0
% 2.58/1.00  sim_joinable_simp:                      0
% 2.58/1.00  sim_ac_normalised:                      0
% 2.58/1.00  sim_smt_subsumption:                    0
% 2.58/1.00  
%------------------------------------------------------------------------------
