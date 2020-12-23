%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:04:56 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 278 expanded)
%              Number of clauses        :   49 (  79 expanded)
%              Number of leaves         :   13 (  59 expanded)
%              Depth                    :   19
%              Number of atoms          :  366 (1036 expanded)
%              Number of equality atoms :  195 ( 396 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( ~ r2_hidden(k1_funct_1(sK3,sK1),sK2)
      & k1_xboole_0 != sK2
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
      & v1_funct_2(sK3,k1_tarski(sK1),sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK1),sK2)
    & k1_xboole_0 != sK2
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
    & v1_funct_2(sK3,k1_tarski(sK1),sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f22,f29])).

fof(f54,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f57,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f58,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))) ),
    inference(definition_unfolding,[],[f54,f57])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X2),X0)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f52,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f53,plain,(
    v1_funct_2(sK3,k1_tarski(sK1),sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f59,plain,(
    v1_funct_2(sK3,k1_enumset1(sK1,sK1,sK1),sK2) ),
    inference(definition_unfolding,[],[f53,f57])).

fof(f9,axiom,(
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

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f55,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f56,plain,(
    ~ r2_hidden(k1_funct_1(sK3,sK1),sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f26,plain,(
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

fof(f27,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f32,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f64,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f32])).

fof(f65,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k1_enumset1(X5,X1,X2)) ),
    inference(equality_resolution,[],[f64])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_11,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_10,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X2),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_251,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X2),X1)
    | ~ v1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_23])).

cnf(c_252,plain,
    ( ~ v5_relat_1(sK3,X0)
    | ~ r2_hidden(X1,k1_relat_1(sK3))
    | r2_hidden(k1_funct_1(sK3,X1),X0)
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_251])).

cnf(c_274,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(sK3))
    | r2_hidden(k1_funct_1(sK3,X3),X4)
    | ~ v1_relat_1(sK3)
    | X4 != X2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_252])).

cnf(c_275,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r2_hidden(X2,k1_relat_1(sK3))
    | r2_hidden(k1_funct_1(sK3,X2),X1)
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_274])).

cnf(c_422,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | r2_hidden(k1_funct_1(sK3,X0),X1)
    | ~ v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X1))
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_275])).

cnf(c_555,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | r2_hidden(k1_funct_1(sK3,X0),X1)
    | ~ v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X1)) ),
    inference(equality_resolution_simp,[status(thm)],[c_422])).

cnf(c_844,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | r2_hidden(X2,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X2),X1) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_555])).

cnf(c_556,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | r2_hidden(X2,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X2),X1) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_555])).

cnf(c_630,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_969,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) = k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_630])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_297,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_21])).

cnf(c_298,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_297])).

cnf(c_964,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_298])).

cnf(c_1053,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))
    | v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_964])).

cnf(c_1054,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))
    | v1_relat_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1053])).

cnf(c_9,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1151,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1152,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1151])).

cnf(c_1182,plain,
    ( r2_hidden(k1_funct_1(sK3,X2),X1) = iProver_top
    | r2_hidden(X2,k1_relat_1(sK3)) != iProver_top
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_844,c_556,c_969,c_1054,c_1152])).

cnf(c_1183,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | r2_hidden(X2,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X2),X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_1182])).

cnf(c_22,negated_conjecture,
    ( v1_funct_2(sK3,k1_enumset1(sK1,sK1,sK1),sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_312,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_21])).

cnf(c_313,plain,
    ( ~ v1_funct_2(sK3,X0,X1)
    | k1_relset_1(X0,X1,sK3) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_312])).

cnf(c_490,plain,
    ( k1_relset_1(X0,X1,sK3) = X0
    | k1_enumset1(sK1,sK1,sK1) != X0
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK2 != X1
    | sK3 != sK3
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_313])).

cnf(c_491,plain,
    ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK3) = k1_enumset1(sK1,sK1,sK1)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_490])).

cnf(c_20,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_492,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))
    | k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK3) = k1_enumset1(sK1,sK1,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_491,c_20])).

cnf(c_493,plain,
    ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK3) = k1_enumset1(sK1,sK1,sK1)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
    inference(renaming,[status(thm)],[c_492])).

cnf(c_554,plain,
    ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK3) = k1_enumset1(sK1,sK1,sK1) ),
    inference(equality_resolution_simp,[status(thm)],[c_493])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_348,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_21])).

cnf(c_349,plain,
    ( k1_relset_1(X0,X1,sK3) = k1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_348])).

cnf(c_1000,plain,
    ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK3) = k1_relat_1(sK3) ),
    inference(equality_resolution,[status(thm)],[c_349])).

cnf(c_1099,plain,
    ( k1_enumset1(sK1,sK1,sK1) = k1_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_554,c_1000])).

cnf(c_1188,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | r2_hidden(X2,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X2),X1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1183,c_1099])).

cnf(c_1195,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0),sK2) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1188])).

cnf(c_19,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(sK3,sK1),sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_846,plain,
    ( r2_hidden(k1_funct_1(sK3,sK1),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1522,plain,
    ( r2_hidden(sK1,k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1195,c_846])).

cnf(c_6,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_849,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1315,plain,
    ( r2_hidden(sK1,k1_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1099,c_849])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1522,c_1315])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:07:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.99/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.02  
% 1.99/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.99/1.02  
% 1.99/1.02  ------  iProver source info
% 1.99/1.02  
% 1.99/1.02  git: date: 2020-06-30 10:37:57 +0100
% 1.99/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.99/1.02  git: non_committed_changes: false
% 1.99/1.02  git: last_make_outside_of_git: false
% 1.99/1.02  
% 1.99/1.02  ------ 
% 1.99/1.02  
% 1.99/1.02  ------ Input Options
% 1.99/1.02  
% 1.99/1.02  --out_options                           all
% 1.99/1.02  --tptp_safe_out                         true
% 1.99/1.02  --problem_path                          ""
% 1.99/1.02  --include_path                          ""
% 1.99/1.02  --clausifier                            res/vclausify_rel
% 1.99/1.02  --clausifier_options                    --mode clausify
% 1.99/1.02  --stdin                                 false
% 1.99/1.02  --stats_out                             all
% 1.99/1.02  
% 1.99/1.02  ------ General Options
% 1.99/1.02  
% 1.99/1.02  --fof                                   false
% 1.99/1.02  --time_out_real                         305.
% 1.99/1.02  --time_out_virtual                      -1.
% 1.99/1.02  --symbol_type_check                     false
% 1.99/1.02  --clausify_out                          false
% 1.99/1.02  --sig_cnt_out                           false
% 1.99/1.02  --trig_cnt_out                          false
% 1.99/1.02  --trig_cnt_out_tolerance                1.
% 1.99/1.02  --trig_cnt_out_sk_spl                   false
% 1.99/1.02  --abstr_cl_out                          false
% 1.99/1.02  
% 1.99/1.02  ------ Global Options
% 1.99/1.02  
% 1.99/1.02  --schedule                              default
% 1.99/1.02  --add_important_lit                     false
% 1.99/1.02  --prop_solver_per_cl                    1000
% 1.99/1.02  --min_unsat_core                        false
% 1.99/1.02  --soft_assumptions                      false
% 1.99/1.02  --soft_lemma_size                       3
% 1.99/1.02  --prop_impl_unit_size                   0
% 1.99/1.02  --prop_impl_unit                        []
% 1.99/1.02  --share_sel_clauses                     true
% 1.99/1.02  --reset_solvers                         false
% 1.99/1.02  --bc_imp_inh                            [conj_cone]
% 1.99/1.02  --conj_cone_tolerance                   3.
% 1.99/1.02  --extra_neg_conj                        none
% 1.99/1.02  --large_theory_mode                     true
% 1.99/1.02  --prolific_symb_bound                   200
% 1.99/1.02  --lt_threshold                          2000
% 1.99/1.02  --clause_weak_htbl                      true
% 1.99/1.02  --gc_record_bc_elim                     false
% 1.99/1.02  
% 1.99/1.02  ------ Preprocessing Options
% 1.99/1.02  
% 1.99/1.02  --preprocessing_flag                    true
% 1.99/1.02  --time_out_prep_mult                    0.1
% 1.99/1.02  --splitting_mode                        input
% 1.99/1.02  --splitting_grd                         true
% 1.99/1.02  --splitting_cvd                         false
% 1.99/1.02  --splitting_cvd_svl                     false
% 1.99/1.02  --splitting_nvd                         32
% 1.99/1.02  --sub_typing                            true
% 1.99/1.02  --prep_gs_sim                           true
% 1.99/1.02  --prep_unflatten                        true
% 1.99/1.02  --prep_res_sim                          true
% 1.99/1.02  --prep_upred                            true
% 1.99/1.02  --prep_sem_filter                       exhaustive
% 1.99/1.02  --prep_sem_filter_out                   false
% 1.99/1.02  --pred_elim                             true
% 1.99/1.02  --res_sim_input                         true
% 1.99/1.02  --eq_ax_congr_red                       true
% 1.99/1.02  --pure_diseq_elim                       true
% 1.99/1.02  --brand_transform                       false
% 1.99/1.02  --non_eq_to_eq                          false
% 1.99/1.02  --prep_def_merge                        true
% 1.99/1.02  --prep_def_merge_prop_impl              false
% 1.99/1.02  --prep_def_merge_mbd                    true
% 1.99/1.02  --prep_def_merge_tr_red                 false
% 1.99/1.02  --prep_def_merge_tr_cl                  false
% 1.99/1.02  --smt_preprocessing                     true
% 1.99/1.02  --smt_ac_axioms                         fast
% 1.99/1.02  --preprocessed_out                      false
% 1.99/1.02  --preprocessed_stats                    false
% 1.99/1.02  
% 1.99/1.02  ------ Abstraction refinement Options
% 1.99/1.02  
% 1.99/1.02  --abstr_ref                             []
% 1.99/1.02  --abstr_ref_prep                        false
% 1.99/1.02  --abstr_ref_until_sat                   false
% 1.99/1.02  --abstr_ref_sig_restrict                funpre
% 1.99/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.99/1.02  --abstr_ref_under                       []
% 1.99/1.02  
% 1.99/1.02  ------ SAT Options
% 1.99/1.02  
% 1.99/1.02  --sat_mode                              false
% 1.99/1.02  --sat_fm_restart_options                ""
% 1.99/1.02  --sat_gr_def                            false
% 1.99/1.02  --sat_epr_types                         true
% 1.99/1.02  --sat_non_cyclic_types                  false
% 1.99/1.02  --sat_finite_models                     false
% 1.99/1.02  --sat_fm_lemmas                         false
% 1.99/1.02  --sat_fm_prep                           false
% 1.99/1.02  --sat_fm_uc_incr                        true
% 1.99/1.02  --sat_out_model                         small
% 1.99/1.02  --sat_out_clauses                       false
% 1.99/1.02  
% 1.99/1.02  ------ QBF Options
% 1.99/1.02  
% 1.99/1.02  --qbf_mode                              false
% 1.99/1.02  --qbf_elim_univ                         false
% 1.99/1.02  --qbf_dom_inst                          none
% 1.99/1.02  --qbf_dom_pre_inst                      false
% 1.99/1.02  --qbf_sk_in                             false
% 1.99/1.02  --qbf_pred_elim                         true
% 1.99/1.02  --qbf_split                             512
% 1.99/1.02  
% 1.99/1.02  ------ BMC1 Options
% 1.99/1.02  
% 1.99/1.02  --bmc1_incremental                      false
% 1.99/1.02  --bmc1_axioms                           reachable_all
% 1.99/1.02  --bmc1_min_bound                        0
% 1.99/1.02  --bmc1_max_bound                        -1
% 1.99/1.02  --bmc1_max_bound_default                -1
% 1.99/1.02  --bmc1_symbol_reachability              true
% 1.99/1.02  --bmc1_property_lemmas                  false
% 1.99/1.02  --bmc1_k_induction                      false
% 1.99/1.02  --bmc1_non_equiv_states                 false
% 1.99/1.02  --bmc1_deadlock                         false
% 1.99/1.02  --bmc1_ucm                              false
% 1.99/1.02  --bmc1_add_unsat_core                   none
% 1.99/1.02  --bmc1_unsat_core_children              false
% 1.99/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.99/1.02  --bmc1_out_stat                         full
% 1.99/1.02  --bmc1_ground_init                      false
% 1.99/1.02  --bmc1_pre_inst_next_state              false
% 1.99/1.02  --bmc1_pre_inst_state                   false
% 1.99/1.02  --bmc1_pre_inst_reach_state             false
% 1.99/1.02  --bmc1_out_unsat_core                   false
% 1.99/1.02  --bmc1_aig_witness_out                  false
% 1.99/1.02  --bmc1_verbose                          false
% 1.99/1.02  --bmc1_dump_clauses_tptp                false
% 1.99/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.99/1.02  --bmc1_dump_file                        -
% 1.99/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.99/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.99/1.02  --bmc1_ucm_extend_mode                  1
% 1.99/1.02  --bmc1_ucm_init_mode                    2
% 1.99/1.02  --bmc1_ucm_cone_mode                    none
% 1.99/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.99/1.02  --bmc1_ucm_relax_model                  4
% 1.99/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.99/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.99/1.02  --bmc1_ucm_layered_model                none
% 1.99/1.02  --bmc1_ucm_max_lemma_size               10
% 1.99/1.02  
% 1.99/1.02  ------ AIG Options
% 1.99/1.02  
% 1.99/1.02  --aig_mode                              false
% 1.99/1.02  
% 1.99/1.02  ------ Instantiation Options
% 1.99/1.02  
% 1.99/1.02  --instantiation_flag                    true
% 1.99/1.02  --inst_sos_flag                         false
% 1.99/1.02  --inst_sos_phase                        true
% 1.99/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.99/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.99/1.02  --inst_lit_sel_side                     num_symb
% 1.99/1.02  --inst_solver_per_active                1400
% 1.99/1.02  --inst_solver_calls_frac                1.
% 1.99/1.02  --inst_passive_queue_type               priority_queues
% 1.99/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.99/1.02  --inst_passive_queues_freq              [25;2]
% 1.99/1.02  --inst_dismatching                      true
% 1.99/1.02  --inst_eager_unprocessed_to_passive     true
% 1.99/1.02  --inst_prop_sim_given                   true
% 1.99/1.02  --inst_prop_sim_new                     false
% 1.99/1.02  --inst_subs_new                         false
% 1.99/1.02  --inst_eq_res_simp                      false
% 1.99/1.02  --inst_subs_given                       false
% 1.99/1.02  --inst_orphan_elimination               true
% 1.99/1.02  --inst_learning_loop_flag               true
% 1.99/1.02  --inst_learning_start                   3000
% 1.99/1.02  --inst_learning_factor                  2
% 1.99/1.02  --inst_start_prop_sim_after_learn       3
% 1.99/1.02  --inst_sel_renew                        solver
% 1.99/1.02  --inst_lit_activity_flag                true
% 1.99/1.02  --inst_restr_to_given                   false
% 1.99/1.02  --inst_activity_threshold               500
% 1.99/1.02  --inst_out_proof                        true
% 1.99/1.02  
% 1.99/1.02  ------ Resolution Options
% 1.99/1.02  
% 1.99/1.02  --resolution_flag                       true
% 1.99/1.02  --res_lit_sel                           adaptive
% 1.99/1.02  --res_lit_sel_side                      none
% 1.99/1.02  --res_ordering                          kbo
% 1.99/1.02  --res_to_prop_solver                    active
% 1.99/1.02  --res_prop_simpl_new                    false
% 1.99/1.02  --res_prop_simpl_given                  true
% 1.99/1.02  --res_passive_queue_type                priority_queues
% 1.99/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.99/1.02  --res_passive_queues_freq               [15;5]
% 1.99/1.02  --res_forward_subs                      full
% 1.99/1.02  --res_backward_subs                     full
% 1.99/1.02  --res_forward_subs_resolution           true
% 1.99/1.02  --res_backward_subs_resolution          true
% 1.99/1.02  --res_orphan_elimination                true
% 1.99/1.02  --res_time_limit                        2.
% 1.99/1.02  --res_out_proof                         true
% 1.99/1.02  
% 1.99/1.02  ------ Superposition Options
% 1.99/1.02  
% 1.99/1.02  --superposition_flag                    true
% 1.99/1.02  --sup_passive_queue_type                priority_queues
% 1.99/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.99/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.99/1.02  --demod_completeness_check              fast
% 1.99/1.02  --demod_use_ground                      true
% 1.99/1.02  --sup_to_prop_solver                    passive
% 1.99/1.02  --sup_prop_simpl_new                    true
% 1.99/1.02  --sup_prop_simpl_given                  true
% 1.99/1.02  --sup_fun_splitting                     false
% 1.99/1.02  --sup_smt_interval                      50000
% 1.99/1.02  
% 1.99/1.02  ------ Superposition Simplification Setup
% 1.99/1.02  
% 1.99/1.02  --sup_indices_passive                   []
% 1.99/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.99/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/1.02  --sup_full_bw                           [BwDemod]
% 1.99/1.02  --sup_immed_triv                        [TrivRules]
% 1.99/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.99/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/1.02  --sup_immed_bw_main                     []
% 1.99/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.99/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.99/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.99/1.02  
% 1.99/1.02  ------ Combination Options
% 1.99/1.02  
% 1.99/1.02  --comb_res_mult                         3
% 1.99/1.02  --comb_sup_mult                         2
% 1.99/1.02  --comb_inst_mult                        10
% 1.99/1.02  
% 1.99/1.02  ------ Debug Options
% 1.99/1.02  
% 1.99/1.02  --dbg_backtrace                         false
% 1.99/1.02  --dbg_dump_prop_clauses                 false
% 1.99/1.02  --dbg_dump_prop_clauses_file            -
% 1.99/1.02  --dbg_out_stat                          false
% 1.99/1.02  ------ Parsing...
% 1.99/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.99/1.02  
% 1.99/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 1.99/1.02  
% 1.99/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.99/1.02  
% 1.99/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.99/1.02  ------ Proving...
% 1.99/1.02  ------ Problem Properties 
% 1.99/1.02  
% 1.99/1.02  
% 1.99/1.02  clauses                                 17
% 1.99/1.02  conjectures                             2
% 1.99/1.02  EPR                                     1
% 1.99/1.02  Horn                                    14
% 1.99/1.02  unary                                   7
% 1.99/1.02  binary                                  1
% 1.99/1.02  lits                                    41
% 1.99/1.02  lits eq                                 26
% 1.99/1.02  fd_pure                                 0
% 1.99/1.02  fd_pseudo                               0
% 1.99/1.02  fd_cond                                 0
% 1.99/1.02  fd_pseudo_cond                          4
% 1.99/1.02  AC symbols                              0
% 1.99/1.02  
% 1.99/1.02  ------ Schedule dynamic 5 is on 
% 1.99/1.02  
% 1.99/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.99/1.02  
% 1.99/1.02  
% 1.99/1.02  ------ 
% 1.99/1.02  Current options:
% 1.99/1.02  ------ 
% 1.99/1.02  
% 1.99/1.02  ------ Input Options
% 1.99/1.02  
% 1.99/1.02  --out_options                           all
% 1.99/1.02  --tptp_safe_out                         true
% 1.99/1.02  --problem_path                          ""
% 1.99/1.02  --include_path                          ""
% 1.99/1.02  --clausifier                            res/vclausify_rel
% 1.99/1.02  --clausifier_options                    --mode clausify
% 1.99/1.02  --stdin                                 false
% 1.99/1.02  --stats_out                             all
% 1.99/1.02  
% 1.99/1.02  ------ General Options
% 1.99/1.02  
% 1.99/1.02  --fof                                   false
% 1.99/1.02  --time_out_real                         305.
% 1.99/1.02  --time_out_virtual                      -1.
% 1.99/1.02  --symbol_type_check                     false
% 1.99/1.02  --clausify_out                          false
% 1.99/1.02  --sig_cnt_out                           false
% 1.99/1.02  --trig_cnt_out                          false
% 1.99/1.02  --trig_cnt_out_tolerance                1.
% 1.99/1.02  --trig_cnt_out_sk_spl                   false
% 1.99/1.02  --abstr_cl_out                          false
% 1.99/1.02  
% 1.99/1.02  ------ Global Options
% 1.99/1.02  
% 1.99/1.02  --schedule                              default
% 1.99/1.02  --add_important_lit                     false
% 1.99/1.02  --prop_solver_per_cl                    1000
% 1.99/1.02  --min_unsat_core                        false
% 1.99/1.02  --soft_assumptions                      false
% 1.99/1.02  --soft_lemma_size                       3
% 1.99/1.02  --prop_impl_unit_size                   0
% 1.99/1.02  --prop_impl_unit                        []
% 1.99/1.02  --share_sel_clauses                     true
% 1.99/1.02  --reset_solvers                         false
% 1.99/1.02  --bc_imp_inh                            [conj_cone]
% 1.99/1.02  --conj_cone_tolerance                   3.
% 1.99/1.02  --extra_neg_conj                        none
% 1.99/1.02  --large_theory_mode                     true
% 1.99/1.02  --prolific_symb_bound                   200
% 1.99/1.02  --lt_threshold                          2000
% 1.99/1.02  --clause_weak_htbl                      true
% 1.99/1.02  --gc_record_bc_elim                     false
% 1.99/1.02  
% 1.99/1.02  ------ Preprocessing Options
% 1.99/1.02  
% 1.99/1.02  --preprocessing_flag                    true
% 1.99/1.02  --time_out_prep_mult                    0.1
% 1.99/1.02  --splitting_mode                        input
% 1.99/1.02  --splitting_grd                         true
% 1.99/1.02  --splitting_cvd                         false
% 1.99/1.02  --splitting_cvd_svl                     false
% 1.99/1.02  --splitting_nvd                         32
% 1.99/1.02  --sub_typing                            true
% 1.99/1.02  --prep_gs_sim                           true
% 1.99/1.02  --prep_unflatten                        true
% 1.99/1.02  --prep_res_sim                          true
% 1.99/1.02  --prep_upred                            true
% 1.99/1.02  --prep_sem_filter                       exhaustive
% 1.99/1.02  --prep_sem_filter_out                   false
% 1.99/1.02  --pred_elim                             true
% 1.99/1.02  --res_sim_input                         true
% 1.99/1.02  --eq_ax_congr_red                       true
% 1.99/1.02  --pure_diseq_elim                       true
% 1.99/1.02  --brand_transform                       false
% 1.99/1.02  --non_eq_to_eq                          false
% 1.99/1.02  --prep_def_merge                        true
% 1.99/1.02  --prep_def_merge_prop_impl              false
% 1.99/1.02  --prep_def_merge_mbd                    true
% 1.99/1.02  --prep_def_merge_tr_red                 false
% 1.99/1.02  --prep_def_merge_tr_cl                  false
% 1.99/1.02  --smt_preprocessing                     true
% 1.99/1.02  --smt_ac_axioms                         fast
% 1.99/1.02  --preprocessed_out                      false
% 1.99/1.02  --preprocessed_stats                    false
% 1.99/1.02  
% 1.99/1.02  ------ Abstraction refinement Options
% 1.99/1.02  
% 1.99/1.02  --abstr_ref                             []
% 1.99/1.02  --abstr_ref_prep                        false
% 1.99/1.02  --abstr_ref_until_sat                   false
% 1.99/1.02  --abstr_ref_sig_restrict                funpre
% 1.99/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.99/1.02  --abstr_ref_under                       []
% 1.99/1.02  
% 1.99/1.02  ------ SAT Options
% 1.99/1.02  
% 1.99/1.02  --sat_mode                              false
% 1.99/1.02  --sat_fm_restart_options                ""
% 1.99/1.02  --sat_gr_def                            false
% 1.99/1.02  --sat_epr_types                         true
% 1.99/1.02  --sat_non_cyclic_types                  false
% 1.99/1.02  --sat_finite_models                     false
% 1.99/1.02  --sat_fm_lemmas                         false
% 1.99/1.02  --sat_fm_prep                           false
% 1.99/1.02  --sat_fm_uc_incr                        true
% 1.99/1.02  --sat_out_model                         small
% 1.99/1.02  --sat_out_clauses                       false
% 1.99/1.02  
% 1.99/1.02  ------ QBF Options
% 1.99/1.02  
% 1.99/1.02  --qbf_mode                              false
% 1.99/1.02  --qbf_elim_univ                         false
% 1.99/1.02  --qbf_dom_inst                          none
% 1.99/1.02  --qbf_dom_pre_inst                      false
% 1.99/1.02  --qbf_sk_in                             false
% 1.99/1.02  --qbf_pred_elim                         true
% 1.99/1.02  --qbf_split                             512
% 1.99/1.02  
% 1.99/1.02  ------ BMC1 Options
% 1.99/1.02  
% 1.99/1.02  --bmc1_incremental                      false
% 1.99/1.02  --bmc1_axioms                           reachable_all
% 1.99/1.02  --bmc1_min_bound                        0
% 1.99/1.02  --bmc1_max_bound                        -1
% 1.99/1.02  --bmc1_max_bound_default                -1
% 1.99/1.02  --bmc1_symbol_reachability              true
% 1.99/1.02  --bmc1_property_lemmas                  false
% 1.99/1.02  --bmc1_k_induction                      false
% 1.99/1.02  --bmc1_non_equiv_states                 false
% 1.99/1.02  --bmc1_deadlock                         false
% 1.99/1.02  --bmc1_ucm                              false
% 1.99/1.02  --bmc1_add_unsat_core                   none
% 1.99/1.02  --bmc1_unsat_core_children              false
% 1.99/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.99/1.02  --bmc1_out_stat                         full
% 1.99/1.02  --bmc1_ground_init                      false
% 1.99/1.02  --bmc1_pre_inst_next_state              false
% 1.99/1.02  --bmc1_pre_inst_state                   false
% 1.99/1.02  --bmc1_pre_inst_reach_state             false
% 1.99/1.02  --bmc1_out_unsat_core                   false
% 1.99/1.02  --bmc1_aig_witness_out                  false
% 1.99/1.02  --bmc1_verbose                          false
% 1.99/1.02  --bmc1_dump_clauses_tptp                false
% 1.99/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.99/1.02  --bmc1_dump_file                        -
% 1.99/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.99/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.99/1.02  --bmc1_ucm_extend_mode                  1
% 1.99/1.02  --bmc1_ucm_init_mode                    2
% 1.99/1.02  --bmc1_ucm_cone_mode                    none
% 1.99/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.99/1.02  --bmc1_ucm_relax_model                  4
% 1.99/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.99/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.99/1.02  --bmc1_ucm_layered_model                none
% 1.99/1.02  --bmc1_ucm_max_lemma_size               10
% 1.99/1.02  
% 1.99/1.02  ------ AIG Options
% 1.99/1.02  
% 1.99/1.02  --aig_mode                              false
% 1.99/1.02  
% 1.99/1.02  ------ Instantiation Options
% 1.99/1.02  
% 1.99/1.02  --instantiation_flag                    true
% 1.99/1.02  --inst_sos_flag                         false
% 1.99/1.02  --inst_sos_phase                        true
% 1.99/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.99/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.99/1.02  --inst_lit_sel_side                     none
% 1.99/1.02  --inst_solver_per_active                1400
% 1.99/1.02  --inst_solver_calls_frac                1.
% 1.99/1.02  --inst_passive_queue_type               priority_queues
% 1.99/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.99/1.02  --inst_passive_queues_freq              [25;2]
% 1.99/1.02  --inst_dismatching                      true
% 1.99/1.02  --inst_eager_unprocessed_to_passive     true
% 1.99/1.02  --inst_prop_sim_given                   true
% 1.99/1.02  --inst_prop_sim_new                     false
% 1.99/1.02  --inst_subs_new                         false
% 1.99/1.02  --inst_eq_res_simp                      false
% 1.99/1.02  --inst_subs_given                       false
% 1.99/1.02  --inst_orphan_elimination               true
% 1.99/1.02  --inst_learning_loop_flag               true
% 1.99/1.02  --inst_learning_start                   3000
% 1.99/1.02  --inst_learning_factor                  2
% 1.99/1.02  --inst_start_prop_sim_after_learn       3
% 1.99/1.02  --inst_sel_renew                        solver
% 1.99/1.02  --inst_lit_activity_flag                true
% 1.99/1.02  --inst_restr_to_given                   false
% 1.99/1.02  --inst_activity_threshold               500
% 1.99/1.02  --inst_out_proof                        true
% 1.99/1.02  
% 1.99/1.02  ------ Resolution Options
% 1.99/1.02  
% 1.99/1.02  --resolution_flag                       false
% 1.99/1.02  --res_lit_sel                           adaptive
% 1.99/1.02  --res_lit_sel_side                      none
% 1.99/1.02  --res_ordering                          kbo
% 1.99/1.02  --res_to_prop_solver                    active
% 1.99/1.02  --res_prop_simpl_new                    false
% 1.99/1.02  --res_prop_simpl_given                  true
% 1.99/1.02  --res_passive_queue_type                priority_queues
% 1.99/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.99/1.02  --res_passive_queues_freq               [15;5]
% 1.99/1.02  --res_forward_subs                      full
% 1.99/1.02  --res_backward_subs                     full
% 1.99/1.02  --res_forward_subs_resolution           true
% 1.99/1.02  --res_backward_subs_resolution          true
% 1.99/1.02  --res_orphan_elimination                true
% 1.99/1.02  --res_time_limit                        2.
% 1.99/1.02  --res_out_proof                         true
% 1.99/1.02  
% 1.99/1.02  ------ Superposition Options
% 1.99/1.02  
% 1.99/1.02  --superposition_flag                    true
% 1.99/1.02  --sup_passive_queue_type                priority_queues
% 1.99/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.99/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.99/1.02  --demod_completeness_check              fast
% 1.99/1.02  --demod_use_ground                      true
% 1.99/1.02  --sup_to_prop_solver                    passive
% 1.99/1.02  --sup_prop_simpl_new                    true
% 1.99/1.02  --sup_prop_simpl_given                  true
% 1.99/1.02  --sup_fun_splitting                     false
% 1.99/1.02  --sup_smt_interval                      50000
% 1.99/1.02  
% 1.99/1.02  ------ Superposition Simplification Setup
% 1.99/1.02  
% 1.99/1.02  --sup_indices_passive                   []
% 1.99/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.99/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/1.02  --sup_full_bw                           [BwDemod]
% 1.99/1.02  --sup_immed_triv                        [TrivRules]
% 1.99/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.99/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/1.02  --sup_immed_bw_main                     []
% 1.99/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.99/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.99/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.99/1.02  
% 1.99/1.02  ------ Combination Options
% 1.99/1.02  
% 1.99/1.02  --comb_res_mult                         3
% 1.99/1.02  --comb_sup_mult                         2
% 1.99/1.02  --comb_inst_mult                        10
% 1.99/1.02  
% 1.99/1.02  ------ Debug Options
% 1.99/1.02  
% 1.99/1.02  --dbg_backtrace                         false
% 1.99/1.02  --dbg_dump_prop_clauses                 false
% 1.99/1.02  --dbg_dump_prop_clauses_file            -
% 1.99/1.02  --dbg_out_stat                          false
% 1.99/1.02  
% 1.99/1.02  
% 1.99/1.02  
% 1.99/1.02  
% 1.99/1.02  ------ Proving...
% 1.99/1.02  
% 1.99/1.02  
% 1.99/1.02  % SZS status Theorem for theBenchmark.p
% 1.99/1.02  
% 1.99/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 1.99/1.02  
% 1.99/1.02  fof(f10,conjecture,(
% 1.99/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 1.99/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.02  
% 1.99/1.02  fof(f11,negated_conjecture,(
% 1.99/1.02    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 1.99/1.02    inference(negated_conjecture,[],[f10])).
% 1.99/1.02  
% 1.99/1.02  fof(f21,plain,(
% 1.99/1.02    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 1.99/1.02    inference(ennf_transformation,[],[f11])).
% 1.99/1.02  
% 1.99/1.02  fof(f22,plain,(
% 1.99/1.02    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 1.99/1.02    inference(flattening,[],[f21])).
% 1.99/1.02  
% 1.99/1.02  fof(f29,plain,(
% 1.99/1.02    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (~r2_hidden(k1_funct_1(sK3,sK1),sK2) & k1_xboole_0 != sK2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK3,k1_tarski(sK1),sK2) & v1_funct_1(sK3))),
% 1.99/1.02    introduced(choice_axiom,[])).
% 1.99/1.02  
% 1.99/1.02  fof(f30,plain,(
% 1.99/1.02    ~r2_hidden(k1_funct_1(sK3,sK1),sK2) & k1_xboole_0 != sK2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK3,k1_tarski(sK1),sK2) & v1_funct_1(sK3)),
% 1.99/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f22,f29])).
% 1.99/1.02  
% 1.99/1.02  fof(f54,plain,(
% 1.99/1.02    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))),
% 1.99/1.02    inference(cnf_transformation,[],[f30])).
% 1.99/1.02  
% 1.99/1.02  fof(f2,axiom,(
% 1.99/1.02    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.99/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.02  
% 1.99/1.02  fof(f39,plain,(
% 1.99/1.02    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.99/1.02    inference(cnf_transformation,[],[f2])).
% 1.99/1.02  
% 1.99/1.02  fof(f3,axiom,(
% 1.99/1.02    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.99/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.02  
% 1.99/1.02  fof(f40,plain,(
% 1.99/1.02    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.99/1.02    inference(cnf_transformation,[],[f3])).
% 1.99/1.02  
% 1.99/1.02  fof(f57,plain,(
% 1.99/1.02    ( ! [X0] : (k1_enumset1(X0,X0,X0) = k1_tarski(X0)) )),
% 1.99/1.02    inference(definition_unfolding,[],[f39,f40])).
% 1.99/1.02  
% 1.99/1.02  fof(f58,plain,(
% 1.99/1.02    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)))),
% 1.99/1.02    inference(definition_unfolding,[],[f54,f57])).
% 1.99/1.02  
% 1.99/1.02  fof(f7,axiom,(
% 1.99/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.99/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.02  
% 1.99/1.02  fof(f12,plain,(
% 1.99/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.99/1.02    inference(pure_predicate_removal,[],[f7])).
% 1.99/1.02  
% 1.99/1.02  fof(f17,plain,(
% 1.99/1.02    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.99/1.02    inference(ennf_transformation,[],[f12])).
% 1.99/1.02  
% 1.99/1.02  fof(f44,plain,(
% 1.99/1.02    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.99/1.02    inference(cnf_transformation,[],[f17])).
% 1.99/1.02  
% 1.99/1.02  fof(f6,axiom,(
% 1.99/1.02    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 1.99/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.02  
% 1.99/1.02  fof(f15,plain,(
% 1.99/1.02    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.99/1.02    inference(ennf_transformation,[],[f6])).
% 1.99/1.02  
% 1.99/1.02  fof(f16,plain,(
% 1.99/1.02    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.99/1.02    inference(flattening,[],[f15])).
% 1.99/1.02  
% 1.99/1.02  fof(f43,plain,(
% 1.99/1.02    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.99/1.02    inference(cnf_transformation,[],[f16])).
% 1.99/1.02  
% 1.99/1.02  fof(f52,plain,(
% 1.99/1.02    v1_funct_1(sK3)),
% 1.99/1.02    inference(cnf_transformation,[],[f30])).
% 1.99/1.02  
% 1.99/1.02  fof(f4,axiom,(
% 1.99/1.02    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.99/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.02  
% 1.99/1.02  fof(f14,plain,(
% 1.99/1.02    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.99/1.02    inference(ennf_transformation,[],[f4])).
% 1.99/1.02  
% 1.99/1.02  fof(f41,plain,(
% 1.99/1.02    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.99/1.02    inference(cnf_transformation,[],[f14])).
% 1.99/1.02  
% 1.99/1.02  fof(f5,axiom,(
% 1.99/1.02    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.99/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.02  
% 1.99/1.02  fof(f42,plain,(
% 1.99/1.02    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.99/1.02    inference(cnf_transformation,[],[f5])).
% 1.99/1.02  
% 1.99/1.02  fof(f53,plain,(
% 1.99/1.02    v1_funct_2(sK3,k1_tarski(sK1),sK2)),
% 1.99/1.02    inference(cnf_transformation,[],[f30])).
% 1.99/1.02  
% 1.99/1.02  fof(f59,plain,(
% 1.99/1.02    v1_funct_2(sK3,k1_enumset1(sK1,sK1,sK1),sK2)),
% 1.99/1.02    inference(definition_unfolding,[],[f53,f57])).
% 1.99/1.02  
% 1.99/1.02  fof(f9,axiom,(
% 1.99/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.99/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.02  
% 1.99/1.02  fof(f19,plain,(
% 1.99/1.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.99/1.02    inference(ennf_transformation,[],[f9])).
% 1.99/1.02  
% 1.99/1.02  fof(f20,plain,(
% 1.99/1.02    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.99/1.02    inference(flattening,[],[f19])).
% 1.99/1.02  
% 1.99/1.02  fof(f28,plain,(
% 1.99/1.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.99/1.02    inference(nnf_transformation,[],[f20])).
% 1.99/1.02  
% 1.99/1.02  fof(f46,plain,(
% 1.99/1.02    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.99/1.02    inference(cnf_transformation,[],[f28])).
% 1.99/1.02  
% 1.99/1.02  fof(f55,plain,(
% 1.99/1.02    k1_xboole_0 != sK2),
% 1.99/1.02    inference(cnf_transformation,[],[f30])).
% 1.99/1.02  
% 1.99/1.02  fof(f8,axiom,(
% 1.99/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.99/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.02  
% 1.99/1.02  fof(f18,plain,(
% 1.99/1.02    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.99/1.02    inference(ennf_transformation,[],[f8])).
% 1.99/1.02  
% 1.99/1.02  fof(f45,plain,(
% 1.99/1.02    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.99/1.02    inference(cnf_transformation,[],[f18])).
% 1.99/1.02  
% 1.99/1.02  fof(f56,plain,(
% 1.99/1.02    ~r2_hidden(k1_funct_1(sK3,sK1),sK2)),
% 1.99/1.02    inference(cnf_transformation,[],[f30])).
% 1.99/1.02  
% 1.99/1.02  fof(f1,axiom,(
% 1.99/1.02    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.99/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.02  
% 1.99/1.02  fof(f13,plain,(
% 1.99/1.02    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.99/1.02    inference(ennf_transformation,[],[f1])).
% 1.99/1.02  
% 1.99/1.02  fof(f23,plain,(
% 1.99/1.02    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.99/1.02    inference(nnf_transformation,[],[f13])).
% 1.99/1.02  
% 1.99/1.02  fof(f24,plain,(
% 1.99/1.02    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.99/1.02    inference(flattening,[],[f23])).
% 1.99/1.02  
% 1.99/1.02  fof(f25,plain,(
% 1.99/1.02    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.99/1.02    inference(rectify,[],[f24])).
% 1.99/1.02  
% 1.99/1.02  fof(f26,plain,(
% 1.99/1.02    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 1.99/1.02    introduced(choice_axiom,[])).
% 1.99/1.02  
% 1.99/1.02  fof(f27,plain,(
% 1.99/1.02    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.99/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 1.99/1.02  
% 1.99/1.02  fof(f32,plain,(
% 1.99/1.02    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.99/1.02    inference(cnf_transformation,[],[f27])).
% 1.99/1.02  
% 1.99/1.02  fof(f64,plain,(
% 1.99/1.02    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X5,X1,X2) != X3) )),
% 1.99/1.02    inference(equality_resolution,[],[f32])).
% 1.99/1.02  
% 1.99/1.02  fof(f65,plain,(
% 1.99/1.02    ( ! [X2,X5,X1] : (r2_hidden(X5,k1_enumset1(X5,X1,X2))) )),
% 1.99/1.02    inference(equality_resolution,[],[f64])).
% 1.99/1.02  
% 1.99/1.02  cnf(c_21,negated_conjecture,
% 1.99/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))) ),
% 1.99/1.02      inference(cnf_transformation,[],[f58]) ).
% 1.99/1.02  
% 1.99/1.02  cnf(c_11,plain,
% 1.99/1.02      ( v5_relat_1(X0,X1)
% 1.99/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 1.99/1.02      inference(cnf_transformation,[],[f44]) ).
% 1.99/1.02  
% 1.99/1.02  cnf(c_10,plain,
% 1.99/1.02      ( ~ v5_relat_1(X0,X1)
% 1.99/1.02      | ~ r2_hidden(X2,k1_relat_1(X0))
% 1.99/1.02      | r2_hidden(k1_funct_1(X0,X2),X1)
% 1.99/1.02      | ~ v1_funct_1(X0)
% 1.99/1.02      | ~ v1_relat_1(X0) ),
% 1.99/1.02      inference(cnf_transformation,[],[f43]) ).
% 1.99/1.02  
% 1.99/1.02  cnf(c_23,negated_conjecture,
% 1.99/1.02      ( v1_funct_1(sK3) ),
% 1.99/1.02      inference(cnf_transformation,[],[f52]) ).
% 1.99/1.02  
% 1.99/1.02  cnf(c_251,plain,
% 1.99/1.02      ( ~ v5_relat_1(X0,X1)
% 1.99/1.02      | ~ r2_hidden(X2,k1_relat_1(X0))
% 1.99/1.02      | r2_hidden(k1_funct_1(X0,X2),X1)
% 1.99/1.02      | ~ v1_relat_1(X0)
% 1.99/1.02      | sK3 != X0 ),
% 1.99/1.02      inference(resolution_lifted,[status(thm)],[c_10,c_23]) ).
% 1.99/1.02  
% 1.99/1.02  cnf(c_252,plain,
% 1.99/1.02      ( ~ v5_relat_1(sK3,X0)
% 1.99/1.02      | ~ r2_hidden(X1,k1_relat_1(sK3))
% 1.99/1.02      | r2_hidden(k1_funct_1(sK3,X1),X0)
% 1.99/1.02      | ~ v1_relat_1(sK3) ),
% 1.99/1.02      inference(unflattening,[status(thm)],[c_251]) ).
% 1.99/1.02  
% 1.99/1.02  cnf(c_274,plain,
% 1.99/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.99/1.02      | ~ r2_hidden(X3,k1_relat_1(sK3))
% 1.99/1.02      | r2_hidden(k1_funct_1(sK3,X3),X4)
% 1.99/1.02      | ~ v1_relat_1(sK3)
% 1.99/1.02      | X4 != X2
% 1.99/1.02      | sK3 != X0 ),
% 1.99/1.02      inference(resolution_lifted,[status(thm)],[c_11,c_252]) ).
% 1.99/1.02  
% 1.99/1.02  cnf(c_275,plain,
% 1.99/1.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.99/1.02      | ~ r2_hidden(X2,k1_relat_1(sK3))
% 1.99/1.02      | r2_hidden(k1_funct_1(sK3,X2),X1)
% 1.99/1.02      | ~ v1_relat_1(sK3) ),
% 1.99/1.02      inference(unflattening,[status(thm)],[c_274]) ).
% 1.99/1.02  
% 1.99/1.02  cnf(c_422,plain,
% 1.99/1.02      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 1.99/1.02      | r2_hidden(k1_funct_1(sK3,X0),X1)
% 1.99/1.02      | ~ v1_relat_1(sK3)
% 1.99/1.02      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X1))
% 1.99/1.02      | sK3 != sK3 ),
% 1.99/1.02      inference(resolution_lifted,[status(thm)],[c_21,c_275]) ).
% 1.99/1.02  
% 1.99/1.02  cnf(c_555,plain,
% 1.99/1.02      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 1.99/1.02      | r2_hidden(k1_funct_1(sK3,X0),X1)
% 1.99/1.02      | ~ v1_relat_1(sK3)
% 1.99/1.02      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X1)) ),
% 1.99/1.02      inference(equality_resolution_simp,[status(thm)],[c_422]) ).
% 1.99/1.02  
% 1.99/1.02  cnf(c_844,plain,
% 1.99/1.02      ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.99/1.02      | r2_hidden(X2,k1_relat_1(sK3)) != iProver_top
% 1.99/1.02      | r2_hidden(k1_funct_1(sK3,X2),X1) = iProver_top
% 1.99/1.02      | v1_relat_1(sK3) != iProver_top ),
% 1.99/1.02      inference(predicate_to_equality,[status(thm)],[c_555]) ).
% 1.99/1.02  
% 1.99/1.02  cnf(c_556,plain,
% 1.99/1.02      ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.99/1.02      | r2_hidden(X2,k1_relat_1(sK3)) != iProver_top
% 1.99/1.02      | r2_hidden(k1_funct_1(sK3,X2),X1) = iProver_top
% 1.99/1.02      | v1_relat_1(sK3) != iProver_top ),
% 1.99/1.02      inference(predicate_to_equality,[status(thm)],[c_555]) ).
% 1.99/1.02  
% 1.99/1.02  cnf(c_630,plain,( X0 = X0 ),theory(equality) ).
% 1.99/1.02  
% 1.99/1.02  cnf(c_969,plain,
% 1.99/1.02      ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) = k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
% 1.99/1.02      inference(instantiation,[status(thm)],[c_630]) ).
% 1.99/1.02  
% 1.99/1.02  cnf(c_8,plain,
% 1.99/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.99/1.02      | ~ v1_relat_1(X1)
% 1.99/1.02      | v1_relat_1(X0) ),
% 1.99/1.02      inference(cnf_transformation,[],[f41]) ).
% 1.99/1.02  
% 1.99/1.02  cnf(c_297,plain,
% 1.99/1.02      ( ~ v1_relat_1(X0)
% 1.99/1.02      | v1_relat_1(X1)
% 1.99/1.02      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(X0)
% 1.99/1.02      | sK3 != X1 ),
% 1.99/1.02      inference(resolution_lifted,[status(thm)],[c_8,c_21]) ).
% 1.99/1.02  
% 1.99/1.02  cnf(c_298,plain,
% 1.99/1.02      ( ~ v1_relat_1(X0)
% 1.99/1.02      | v1_relat_1(sK3)
% 1.99/1.02      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(X0) ),
% 1.99/1.02      inference(unflattening,[status(thm)],[c_297]) ).
% 1.99/1.02  
% 1.99/1.02  cnf(c_964,plain,
% 1.99/1.02      ( ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 1.99/1.02      | v1_relat_1(sK3)
% 1.99/1.02      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 1.99/1.02      inference(instantiation,[status(thm)],[c_298]) ).
% 1.99/1.02  
% 1.99/1.02  cnf(c_1053,plain,
% 1.99/1.02      ( ~ v1_relat_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))
% 1.99/1.02      | v1_relat_1(sK3)
% 1.99/1.02      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
% 1.99/1.02      inference(instantiation,[status(thm)],[c_964]) ).
% 1.99/1.02  
% 1.99/1.02  cnf(c_1054,plain,
% 1.99/1.02      ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))
% 1.99/1.02      | v1_relat_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != iProver_top
% 1.99/1.02      | v1_relat_1(sK3) = iProver_top ),
% 1.99/1.02      inference(predicate_to_equality,[status(thm)],[c_1053]) ).
% 1.99/1.02  
% 1.99/1.02  cnf(c_9,plain,
% 1.99/1.02      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 1.99/1.02      inference(cnf_transformation,[],[f42]) ).
% 1.99/1.02  
% 1.99/1.02  cnf(c_1151,plain,
% 1.99/1.02      ( v1_relat_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
% 1.99/1.02      inference(instantiation,[status(thm)],[c_9]) ).
% 1.99/1.02  
% 1.99/1.02  cnf(c_1152,plain,
% 1.99/1.02      ( v1_relat_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) = iProver_top ),
% 1.99/1.02      inference(predicate_to_equality,[status(thm)],[c_1151]) ).
% 1.99/1.02  
% 1.99/1.02  cnf(c_1182,plain,
% 1.99/1.02      ( r2_hidden(k1_funct_1(sK3,X2),X1) = iProver_top
% 1.99/1.02      | r2_hidden(X2,k1_relat_1(sK3)) != iProver_top
% 1.99/1.02      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 1.99/1.02      inference(global_propositional_subsumption,
% 1.99/1.02                [status(thm)],
% 1.99/1.02                [c_844,c_556,c_969,c_1054,c_1152]) ).
% 1.99/1.02  
% 1.99/1.02  cnf(c_1183,plain,
% 1.99/1.02      ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.99/1.02      | r2_hidden(X2,k1_relat_1(sK3)) != iProver_top
% 1.99/1.02      | r2_hidden(k1_funct_1(sK3,X2),X1) = iProver_top ),
% 1.99/1.02      inference(renaming,[status(thm)],[c_1182]) ).
% 1.99/1.02  
% 1.99/1.02  cnf(c_22,negated_conjecture,
% 1.99/1.02      ( v1_funct_2(sK3,k1_enumset1(sK1,sK1,sK1),sK2) ),
% 1.99/1.02      inference(cnf_transformation,[],[f59]) ).
% 1.99/1.02  
% 1.99/1.02  cnf(c_18,plain,
% 1.99/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 1.99/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.99/1.02      | k1_relset_1(X1,X2,X0) = X1
% 1.99/1.02      | k1_xboole_0 = X2 ),
% 1.99/1.02      inference(cnf_transformation,[],[f46]) ).
% 1.99/1.02  
% 1.99/1.02  cnf(c_312,plain,
% 1.99/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 1.99/1.02      | k1_relset_1(X1,X2,X0) = X1
% 1.99/1.02      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 1.99/1.02      | sK3 != X0
% 1.99/1.02      | k1_xboole_0 = X2 ),
% 1.99/1.02      inference(resolution_lifted,[status(thm)],[c_18,c_21]) ).
% 1.99/1.02  
% 1.99/1.02  cnf(c_313,plain,
% 1.99/1.02      ( ~ v1_funct_2(sK3,X0,X1)
% 1.99/1.02      | k1_relset_1(X0,X1,sK3) = X0
% 1.99/1.02      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.99/1.02      | k1_xboole_0 = X1 ),
% 1.99/1.02      inference(unflattening,[status(thm)],[c_312]) ).
% 1.99/1.02  
% 1.99/1.02  cnf(c_490,plain,
% 1.99/1.02      ( k1_relset_1(X0,X1,sK3) = X0
% 1.99/1.02      | k1_enumset1(sK1,sK1,sK1) != X0
% 1.99/1.02      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.99/1.02      | sK2 != X1
% 1.99/1.02      | sK3 != sK3
% 1.99/1.02      | k1_xboole_0 = X1 ),
% 1.99/1.02      inference(resolution_lifted,[status(thm)],[c_22,c_313]) ).
% 1.99/1.02  
% 1.99/1.02  cnf(c_491,plain,
% 1.99/1.02      ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK3) = k1_enumset1(sK1,sK1,sK1)
% 1.99/1.02      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))
% 1.99/1.02      | k1_xboole_0 = sK2 ),
% 1.99/1.02      inference(unflattening,[status(thm)],[c_490]) ).
% 1.99/1.02  
% 1.99/1.02  cnf(c_20,negated_conjecture,
% 1.99/1.02      ( k1_xboole_0 != sK2 ),
% 1.99/1.02      inference(cnf_transformation,[],[f55]) ).
% 1.99/1.02  
% 1.99/1.02  cnf(c_492,plain,
% 1.99/1.02      ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))
% 1.99/1.02      | k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK3) = k1_enumset1(sK1,sK1,sK1) ),
% 1.99/1.02      inference(global_propositional_subsumption,
% 1.99/1.02                [status(thm)],
% 1.99/1.02                [c_491,c_20]) ).
% 1.99/1.02  
% 1.99/1.02  cnf(c_493,plain,
% 1.99/1.02      ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK3) = k1_enumset1(sK1,sK1,sK1)
% 1.99/1.02      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
% 1.99/1.02      inference(renaming,[status(thm)],[c_492]) ).
% 1.99/1.02  
% 1.99/1.02  cnf(c_554,plain,
% 1.99/1.02      ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK3) = k1_enumset1(sK1,sK1,sK1) ),
% 1.99/1.02      inference(equality_resolution_simp,[status(thm)],[c_493]) ).
% 1.99/1.02  
% 1.99/1.02  cnf(c_12,plain,
% 1.99/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.99/1.02      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 1.99/1.02      inference(cnf_transformation,[],[f45]) ).
% 1.99/1.02  
% 1.99/1.02  cnf(c_348,plain,
% 1.99/1.02      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 1.99/1.02      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.99/1.02      | sK3 != X2 ),
% 1.99/1.02      inference(resolution_lifted,[status(thm)],[c_12,c_21]) ).
% 1.99/1.02  
% 1.99/1.02  cnf(c_349,plain,
% 1.99/1.02      ( k1_relset_1(X0,X1,sK3) = k1_relat_1(sK3)
% 1.99/1.02      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 1.99/1.02      inference(unflattening,[status(thm)],[c_348]) ).
% 1.99/1.02  
% 1.99/1.02  cnf(c_1000,plain,
% 1.99/1.02      ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK3) = k1_relat_1(sK3) ),
% 1.99/1.02      inference(equality_resolution,[status(thm)],[c_349]) ).
% 1.99/1.02  
% 1.99/1.02  cnf(c_1099,plain,
% 1.99/1.02      ( k1_enumset1(sK1,sK1,sK1) = k1_relat_1(sK3) ),
% 1.99/1.02      inference(light_normalisation,[status(thm)],[c_554,c_1000]) ).
% 1.99/1.02  
% 1.99/1.02  cnf(c_1188,plain,
% 1.99/1.02      ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.99/1.02      | r2_hidden(X2,k1_relat_1(sK3)) != iProver_top
% 1.99/1.02      | r2_hidden(k1_funct_1(sK3,X2),X1) = iProver_top ),
% 1.99/1.02      inference(light_normalisation,[status(thm)],[c_1183,c_1099]) ).
% 1.99/1.02  
% 1.99/1.02  cnf(c_1195,plain,
% 1.99/1.02      ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 1.99/1.02      | r2_hidden(k1_funct_1(sK3,X0),sK2) = iProver_top ),
% 1.99/1.02      inference(equality_resolution,[status(thm)],[c_1188]) ).
% 1.99/1.02  
% 1.99/1.02  cnf(c_19,negated_conjecture,
% 1.99/1.02      ( ~ r2_hidden(k1_funct_1(sK3,sK1),sK2) ),
% 1.99/1.02      inference(cnf_transformation,[],[f56]) ).
% 1.99/1.02  
% 1.99/1.02  cnf(c_846,plain,
% 1.99/1.02      ( r2_hidden(k1_funct_1(sK3,sK1),sK2) != iProver_top ),
% 1.99/1.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.99/1.02  
% 1.99/1.02  cnf(c_1522,plain,
% 1.99/1.02      ( r2_hidden(sK1,k1_relat_1(sK3)) != iProver_top ),
% 1.99/1.02      inference(superposition,[status(thm)],[c_1195,c_846]) ).
% 1.99/1.02  
% 1.99/1.02  cnf(c_6,plain,
% 1.99/1.02      ( r2_hidden(X0,k1_enumset1(X0,X1,X2)) ),
% 1.99/1.02      inference(cnf_transformation,[],[f65]) ).
% 1.99/1.02  
% 1.99/1.02  cnf(c_849,plain,
% 1.99/1.02      ( r2_hidden(X0,k1_enumset1(X0,X1,X2)) = iProver_top ),
% 1.99/1.02      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 1.99/1.02  
% 1.99/1.02  cnf(c_1315,plain,
% 1.99/1.02      ( r2_hidden(sK1,k1_relat_1(sK3)) = iProver_top ),
% 1.99/1.02      inference(superposition,[status(thm)],[c_1099,c_849]) ).
% 1.99/1.02  
% 1.99/1.02  cnf(contradiction,plain,
% 1.99/1.02      ( $false ),
% 1.99/1.02      inference(minisat,[status(thm)],[c_1522,c_1315]) ).
% 1.99/1.02  
% 1.99/1.02  
% 1.99/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 1.99/1.02  
% 1.99/1.02  ------                               Statistics
% 1.99/1.02  
% 1.99/1.02  ------ General
% 1.99/1.02  
% 1.99/1.02  abstr_ref_over_cycles:                  0
% 1.99/1.02  abstr_ref_under_cycles:                 0
% 1.99/1.02  gc_basic_clause_elim:                   0
% 1.99/1.02  forced_gc_time:                         0
% 1.99/1.02  parsing_time:                           0.012
% 1.99/1.02  unif_index_cands_time:                  0.
% 1.99/1.02  unif_index_add_time:                    0.
% 1.99/1.02  orderings_time:                         0.
% 1.99/1.02  out_proof_time:                         0.011
% 1.99/1.02  total_time:                             0.113
% 1.99/1.02  num_of_symbols:                         48
% 1.99/1.02  num_of_terms:                           1581
% 1.99/1.02  
% 1.99/1.02  ------ Preprocessing
% 1.99/1.02  
% 1.99/1.02  num_of_splits:                          0
% 1.99/1.02  num_of_split_atoms:                     0
% 1.99/1.02  num_of_reused_defs:                     0
% 1.99/1.02  num_eq_ax_congr_red:                    17
% 1.99/1.02  num_of_sem_filtered_clauses:            1
% 1.99/1.02  num_of_subtypes:                        0
% 1.99/1.02  monotx_restored_types:                  0
% 1.99/1.02  sat_num_of_epr_types:                   0
% 1.99/1.02  sat_num_of_non_cyclic_types:            0
% 1.99/1.02  sat_guarded_non_collapsed_types:        0
% 1.99/1.02  num_pure_diseq_elim:                    0
% 1.99/1.02  simp_replaced_by:                       0
% 1.99/1.02  res_preprocessed:                       96
% 1.99/1.02  prep_upred:                             0
% 1.99/1.02  prep_unflattend:                        27
% 1.99/1.02  smt_new_axioms:                         0
% 1.99/1.02  pred_elim_cands:                        2
% 1.99/1.02  pred_elim:                              4
% 1.99/1.02  pred_elim_cl:                           7
% 1.99/1.02  pred_elim_cycles:                       6
% 1.99/1.02  merged_defs:                            0
% 1.99/1.02  merged_defs_ncl:                        0
% 1.99/1.02  bin_hyper_res:                          0
% 1.99/1.02  prep_cycles:                            4
% 1.99/1.02  pred_elim_time:                         0.011
% 1.99/1.02  splitting_time:                         0.
% 1.99/1.02  sem_filter_time:                        0.
% 1.99/1.02  monotx_time:                            0.001
% 1.99/1.02  subtype_inf_time:                       0.
% 1.99/1.02  
% 1.99/1.02  ------ Problem properties
% 1.99/1.02  
% 1.99/1.02  clauses:                                17
% 1.99/1.02  conjectures:                            2
% 1.99/1.02  epr:                                    1
% 1.99/1.02  horn:                                   14
% 1.99/1.02  ground:                                 5
% 1.99/1.02  unary:                                  7
% 1.99/1.02  binary:                                 1
% 1.99/1.02  lits:                                   41
% 1.99/1.02  lits_eq:                                26
% 1.99/1.02  fd_pure:                                0
% 1.99/1.02  fd_pseudo:                              0
% 1.99/1.02  fd_cond:                                0
% 1.99/1.02  fd_pseudo_cond:                         4
% 1.99/1.02  ac_symbols:                             0
% 1.99/1.02  
% 1.99/1.02  ------ Propositional Solver
% 1.99/1.02  
% 1.99/1.02  prop_solver_calls:                      26
% 1.99/1.02  prop_fast_solver_calls:                 578
% 1.99/1.02  smt_solver_calls:                       0
% 1.99/1.02  smt_fast_solver_calls:                  0
% 1.99/1.02  prop_num_of_clauses:                    418
% 1.99/1.02  prop_preprocess_simplified:             2716
% 1.99/1.02  prop_fo_subsumed:                       7
% 1.99/1.02  prop_solver_time:                       0.
% 1.99/1.02  smt_solver_time:                        0.
% 1.99/1.02  smt_fast_solver_time:                   0.
% 1.99/1.02  prop_fast_solver_time:                  0.
% 1.99/1.02  prop_unsat_core_time:                   0.
% 1.99/1.02  
% 1.99/1.02  ------ QBF
% 1.99/1.02  
% 1.99/1.02  qbf_q_res:                              0
% 1.99/1.02  qbf_num_tautologies:                    0
% 1.99/1.02  qbf_prep_cycles:                        0
% 1.99/1.02  
% 1.99/1.02  ------ BMC1
% 1.99/1.02  
% 1.99/1.02  bmc1_current_bound:                     -1
% 1.99/1.02  bmc1_last_solved_bound:                 -1
% 1.99/1.02  bmc1_unsat_core_size:                   -1
% 1.99/1.02  bmc1_unsat_core_parents_size:           -1
% 1.99/1.02  bmc1_merge_next_fun:                    0
% 1.99/1.02  bmc1_unsat_core_clauses_time:           0.
% 1.99/1.02  
% 1.99/1.02  ------ Instantiation
% 1.99/1.02  
% 1.99/1.02  inst_num_of_clauses:                    129
% 1.99/1.02  inst_num_in_passive:                    30
% 1.99/1.02  inst_num_in_active:                     88
% 1.99/1.02  inst_num_in_unprocessed:                11
% 1.99/1.02  inst_num_of_loops:                      90
% 1.99/1.02  inst_num_of_learning_restarts:          0
% 1.99/1.02  inst_num_moves_active_passive:          0
% 1.99/1.02  inst_lit_activity:                      0
% 1.99/1.02  inst_lit_activity_moves:                0
% 1.99/1.02  inst_num_tautologies:                   0
% 1.99/1.02  inst_num_prop_implied:                  0
% 1.99/1.02  inst_num_existing_simplified:           0
% 1.99/1.02  inst_num_eq_res_simplified:             0
% 1.99/1.02  inst_num_child_elim:                    0
% 1.99/1.02  inst_num_of_dismatching_blockings:      12
% 1.99/1.02  inst_num_of_non_proper_insts:           112
% 1.99/1.02  inst_num_of_duplicates:                 0
% 1.99/1.02  inst_inst_num_from_inst_to_res:         0
% 1.99/1.02  inst_dismatching_checking_time:         0.
% 1.99/1.02  
% 1.99/1.02  ------ Resolution
% 1.99/1.02  
% 1.99/1.02  res_num_of_clauses:                     0
% 1.99/1.02  res_num_in_passive:                     0
% 1.99/1.02  res_num_in_active:                      0
% 1.99/1.02  res_num_of_loops:                       100
% 1.99/1.02  res_forward_subset_subsumed:            33
% 1.99/1.02  res_backward_subset_subsumed:           0
% 1.99/1.02  res_forward_subsumed:                   0
% 1.99/1.02  res_backward_subsumed:                  0
% 1.99/1.02  res_forward_subsumption_resolution:     0
% 1.99/1.02  res_backward_subsumption_resolution:    0
% 1.99/1.02  res_clause_to_clause_subsumption:       50
% 1.99/1.02  res_orphan_elimination:                 0
% 1.99/1.02  res_tautology_del:                      10
% 1.99/1.02  res_num_eq_res_simplified:              2
% 1.99/1.02  res_num_sel_changes:                    0
% 1.99/1.02  res_moves_from_active_to_pass:          0
% 1.99/1.02  
% 1.99/1.02  ------ Superposition
% 1.99/1.02  
% 1.99/1.02  sup_time_total:                         0.
% 1.99/1.02  sup_time_generating:                    0.
% 1.99/1.02  sup_time_sim_full:                      0.
% 1.99/1.02  sup_time_sim_immed:                     0.
% 1.99/1.02  
% 1.99/1.02  sup_num_of_clauses:                     21
% 1.99/1.02  sup_num_in_active:                      15
% 1.99/1.02  sup_num_in_passive:                     6
% 1.99/1.02  sup_num_of_loops:                       17
% 1.99/1.02  sup_fw_superposition:                   3
% 1.99/1.02  sup_bw_superposition:                   1
% 1.99/1.02  sup_immediate_simplified:               0
% 1.99/1.02  sup_given_eliminated:                   0
% 1.99/1.02  comparisons_done:                       0
% 1.99/1.02  comparisons_avoided:                    0
% 1.99/1.02  
% 1.99/1.02  ------ Simplifications
% 1.99/1.02  
% 1.99/1.02  
% 1.99/1.02  sim_fw_subset_subsumed:                 0
% 1.99/1.02  sim_bw_subset_subsumed:                 0
% 1.99/1.02  sim_fw_subsumed:                        0
% 1.99/1.02  sim_bw_subsumed:                        0
% 1.99/1.02  sim_fw_subsumption_res:                 0
% 1.99/1.02  sim_bw_subsumption_res:                 0
% 1.99/1.02  sim_tautology_del:                      0
% 1.99/1.02  sim_eq_tautology_del:                   0
% 1.99/1.02  sim_eq_res_simp:                        0
% 1.99/1.02  sim_fw_demodulated:                     0
% 1.99/1.02  sim_bw_demodulated:                     3
% 1.99/1.02  sim_light_normalised:                   2
% 1.99/1.02  sim_joinable_taut:                      0
% 1.99/1.02  sim_joinable_simp:                      0
% 1.99/1.02  sim_ac_normalised:                      0
% 1.99/1.02  sim_smt_subsumption:                    0
% 1.99/1.02  
%------------------------------------------------------------------------------
