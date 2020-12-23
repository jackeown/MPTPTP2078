%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:12 EST 2020

% Result     : Theorem 2.92s
% Output     : CNFRefutation 2.92s
% Verified   : 
% Statistics : Number of formulae       :  151 (1078 expanded)
%              Number of clauses        :   68 ( 200 expanded)
%              Number of leaves         :   24 ( 299 expanded)
%              Depth                    :   18
%              Number of atoms          :  546 (2846 expanded)
%              Number of equality atoms :  323 (1717 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f38])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK0(X0,X1,X2) != X1
            & sK0(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( sK0(X0,X1,X2) = X1
          | sK0(X0,X1,X2) = X0
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK0(X0,X1,X2) != X1
              & sK0(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( sK0(X0,X1,X2) = X1
            | sK0(X0,X1,X2) = X0
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f98,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f62,f63])).

fof(f103,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f57,f98])).

fof(f119,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f103])).

fof(f120,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_enumset1(X0,X0,X0,X4)) ),
    inference(equality_resolution,[],[f119])).

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

fof(f52,plain,
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

fof(f53,plain,
    ( k1_tarski(k1_funct_1(sK5,sK3)) != k2_relset_1(k1_tarski(sK3),sK4,sK5)
    & k1_xboole_0 != sK4
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4)))
    & v1_funct_2(sK5,k1_tarski(sK3),sK4)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f37,f52])).

fof(f95,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4))) ),
    inference(cnf_transformation,[],[f53])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f99,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f61,f98])).

fof(f117,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) ),
    inference(definition_unfolding,[],[f95,f99])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f6])).

fof(f43,plain,(
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

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f64,plain,(
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
    inference(cnf_transformation,[],[f44])).

fof(f114,plain,(
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
    inference(definition_unfolding,[],[f64,f63,f98,f98,f98,f99,f99,f99,f63])).

fof(f97,plain,(
    k1_tarski(k1_funct_1(sK5,sK3)) != k2_relset_1(k1_tarski(sK3),sK4,sK5) ),
    inference(cnf_transformation,[],[f53])).

fof(f116,plain,(
    k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) ),
    inference(definition_unfolding,[],[f97,f99,f99])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f115,plain,(
    ! [X0,X1] :
      ( k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f79,f99,f99])).

fof(f93,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f53])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f77,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

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
    inference(nnf_transformation,[],[f35])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f94,plain,(
    v1_funct_2(sK5,k1_tarski(sK3),sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f118,plain,(
    v1_funct_2(sK5,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
    inference(definition_unfolding,[],[f94,f99])).

fof(f96,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f53])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f49,plain,(
    ! [X2,X1] :
      ( ? [X5] :
          ( ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X2)
          & r2_hidden(X5,X1) )
     => ( ! [X6] : ~ r2_hidden(k4_tarski(sK2(X1,X2),X6),X2)
        & r2_hidden(sK2(X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X3,X2] :
      ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
     => r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ( ! [X6] : ~ r2_hidden(k4_tarski(sK2(X1,X2),X6),X2)
            & r2_hidden(sK2(X1,X2),X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f47,f49,f48])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2)
      | ~ r2_hidden(X3,X1)
      | k1_relset_1(X1,X0,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f12,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_4,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_2102,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_2080,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_25,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_19,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_447,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_25,c_19])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_451,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_447,c_24])).

cnf(c_452,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_451])).

cnf(c_2078,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_452])).

cnf(c_2449,plain,
    ( r1_tarski(k1_relat_1(sK5),k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2080,c_2078])).

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
    inference(cnf_transformation,[],[f114])).

cnf(c_2091,plain,
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

cnf(c_3728,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_relat_1(sK5)
    | k1_relat_1(sK5) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2449,c_2091])).

cnf(c_36,negated_conjecture,
    ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_2336,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2362,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))
    | k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_1553,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2355,plain,
    ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != X0
    | k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) = k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5)
    | k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) != X0 ),
    inference(instantiation,[status(thm)],[c_1553])).

cnf(c_2471,plain,
    ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) = k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5)
    | k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relat_1(sK5)
    | k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) != k2_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_2355])).

cnf(c_22,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_40,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_428,plain,
    ( ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_40])).

cnf(c_429,plain,
    ( ~ v1_relat_1(sK5)
    | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5)
    | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_428])).

cnf(c_2762,plain,
    ( ~ v1_relat_1(sK5)
    | k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) = k2_relat_1(sK5)
    | k2_enumset1(sK3,sK3,sK3,sK3) != k1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_429])).

cnf(c_4233,plain,
    ( k1_relat_1(sK5) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3728,c_38,c_36,c_2336,c_2362,c_2471,c_2762])).

cnf(c_21,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2087,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4244,plain,
    ( sK5 = k1_xboole_0
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4233,c_2087])).

cnf(c_2514,plain,
    ( ~ v1_relat_1(sK5)
    | k1_relat_1(sK5) != k1_xboole_0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1552,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2529,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_1552])).

cnf(c_2720,plain,
    ( X0 != X1
    | sK5 != X1
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_1553])).

cnf(c_3831,plain,
    ( X0 != sK5
    | sK5 = X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_2720])).

cnf(c_3832,plain,
    ( sK5 != sK5
    | sK5 = k1_xboole_0
    | k1_xboole_0 != sK5 ),
    inference(instantiation,[status(thm)],[c_3831])).

cnf(c_4644,plain,
    ( sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4244,c_38,c_36,c_2336,c_2362,c_2471,c_2514,c_2529,c_2762,c_3728,c_3832])).

cnf(c_35,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_39,negated_conjecture,
    ( v1_funct_2(sK5,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_565,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_enumset1(sK3,sK3,sK3,sK3) != X1
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X2
    | sK5 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_35,c_39])).

cnf(c_566,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))
    | k1_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_enumset1(sK3,sK3,sK3,sK3)
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_565])).

cnf(c_37,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_568,plain,
    ( k1_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_566,c_38,c_37])).

cnf(c_4654,plain,
    ( k1_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0) = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(demodulation,[status(thm)],[c_4644,c_568])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k4_tarski(X3,sK1(X0,X3)),X0)
    | k1_relset_1(X1,X2,X0) != X1 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2083,plain,
    ( k1_relset_1(X0,X1,X2) != X0
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r2_hidden(X3,X0) != iProver_top
    | r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_5113,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) != iProver_top
    | r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4654,c_2083])).

cnf(c_43,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_2797,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) = k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) ),
    inference(instantiation,[status(thm)],[c_1552])).

cnf(c_1558,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2396,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))
    | X1 != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))
    | X0 != sK5 ),
    inference(instantiation,[status(thm)],[c_1558])).

cnf(c_4815,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))
    | X0 != sK5
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) ),
    inference(instantiation,[status(thm)],[c_2396])).

cnf(c_4816,plain,
    ( X0 != sK5
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4815])).

cnf(c_4818,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))
    | k1_xboole_0 != sK5
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4816])).

cnf(c_5304,plain,
    ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5113,c_38,c_43,c_36,c_2336,c_2362,c_2471,c_2514,c_2762,c_2797,c_3728,c_4818])).

cnf(c_17,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2089,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3531,plain,
    ( m1_subset_1(X0,k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2080,c_2089])).

cnf(c_4649,plain,
    ( m1_subset_1(X0,k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4644,c_3531])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_23,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_585,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_23])).

cnf(c_586,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_585])).

cnf(c_587,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_586])).

cnf(c_4712,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4649,c_587])).

cnf(c_5312,plain,
    ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5304,c_4712])).

cnf(c_5317,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_2102,c_5312])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:34:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.92/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.92/0.99  
% 2.92/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.92/0.99  
% 2.92/0.99  ------  iProver source info
% 2.92/0.99  
% 2.92/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.92/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.92/0.99  git: non_committed_changes: false
% 2.92/0.99  git: last_make_outside_of_git: false
% 2.92/0.99  
% 2.92/0.99  ------ 
% 2.92/0.99  
% 2.92/0.99  ------ Input Options
% 2.92/0.99  
% 2.92/0.99  --out_options                           all
% 2.92/0.99  --tptp_safe_out                         true
% 2.92/0.99  --problem_path                          ""
% 2.92/0.99  --include_path                          ""
% 2.92/0.99  --clausifier                            res/vclausify_rel
% 2.92/0.99  --clausifier_options                    --mode clausify
% 2.92/0.99  --stdin                                 false
% 2.92/0.99  --stats_out                             all
% 2.92/0.99  
% 2.92/0.99  ------ General Options
% 2.92/0.99  
% 2.92/0.99  --fof                                   false
% 2.92/0.99  --time_out_real                         305.
% 2.92/0.99  --time_out_virtual                      -1.
% 2.92/0.99  --symbol_type_check                     false
% 2.92/0.99  --clausify_out                          false
% 2.92/0.99  --sig_cnt_out                           false
% 2.92/0.99  --trig_cnt_out                          false
% 2.92/0.99  --trig_cnt_out_tolerance                1.
% 2.92/0.99  --trig_cnt_out_sk_spl                   false
% 2.92/0.99  --abstr_cl_out                          false
% 2.92/0.99  
% 2.92/0.99  ------ Global Options
% 2.92/0.99  
% 2.92/0.99  --schedule                              default
% 2.92/0.99  --add_important_lit                     false
% 2.92/0.99  --prop_solver_per_cl                    1000
% 2.92/0.99  --min_unsat_core                        false
% 2.92/0.99  --soft_assumptions                      false
% 2.92/0.99  --soft_lemma_size                       3
% 2.92/0.99  --prop_impl_unit_size                   0
% 2.92/0.99  --prop_impl_unit                        []
% 2.92/0.99  --share_sel_clauses                     true
% 2.92/0.99  --reset_solvers                         false
% 2.92/0.99  --bc_imp_inh                            [conj_cone]
% 2.92/0.99  --conj_cone_tolerance                   3.
% 2.92/0.99  --extra_neg_conj                        none
% 2.92/0.99  --large_theory_mode                     true
% 2.92/0.99  --prolific_symb_bound                   200
% 2.92/0.99  --lt_threshold                          2000
% 2.92/0.99  --clause_weak_htbl                      true
% 2.92/0.99  --gc_record_bc_elim                     false
% 2.92/0.99  
% 2.92/0.99  ------ Preprocessing Options
% 2.92/0.99  
% 2.92/0.99  --preprocessing_flag                    true
% 2.92/0.99  --time_out_prep_mult                    0.1
% 2.92/0.99  --splitting_mode                        input
% 2.92/0.99  --splitting_grd                         true
% 2.92/0.99  --splitting_cvd                         false
% 2.92/0.99  --splitting_cvd_svl                     false
% 2.92/0.99  --splitting_nvd                         32
% 2.92/0.99  --sub_typing                            true
% 2.92/0.99  --prep_gs_sim                           true
% 2.92/0.99  --prep_unflatten                        true
% 2.92/0.99  --prep_res_sim                          true
% 2.92/0.99  --prep_upred                            true
% 2.92/0.99  --prep_sem_filter                       exhaustive
% 2.92/0.99  --prep_sem_filter_out                   false
% 2.92/0.99  --pred_elim                             true
% 2.92/0.99  --res_sim_input                         true
% 2.92/0.99  --eq_ax_congr_red                       true
% 2.92/0.99  --pure_diseq_elim                       true
% 2.92/0.99  --brand_transform                       false
% 2.92/0.99  --non_eq_to_eq                          false
% 2.92/0.99  --prep_def_merge                        true
% 2.92/0.99  --prep_def_merge_prop_impl              false
% 2.92/0.99  --prep_def_merge_mbd                    true
% 2.92/0.99  --prep_def_merge_tr_red                 false
% 2.92/0.99  --prep_def_merge_tr_cl                  false
% 2.92/0.99  --smt_preprocessing                     true
% 2.92/0.99  --smt_ac_axioms                         fast
% 2.92/0.99  --preprocessed_out                      false
% 2.92/0.99  --preprocessed_stats                    false
% 2.92/0.99  
% 2.92/0.99  ------ Abstraction refinement Options
% 2.92/0.99  
% 2.92/0.99  --abstr_ref                             []
% 2.92/0.99  --abstr_ref_prep                        false
% 2.92/0.99  --abstr_ref_until_sat                   false
% 2.92/0.99  --abstr_ref_sig_restrict                funpre
% 2.92/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.92/0.99  --abstr_ref_under                       []
% 2.92/0.99  
% 2.92/0.99  ------ SAT Options
% 2.92/0.99  
% 2.92/0.99  --sat_mode                              false
% 2.92/0.99  --sat_fm_restart_options                ""
% 2.92/0.99  --sat_gr_def                            false
% 2.92/0.99  --sat_epr_types                         true
% 2.92/0.99  --sat_non_cyclic_types                  false
% 2.92/0.99  --sat_finite_models                     false
% 2.92/0.99  --sat_fm_lemmas                         false
% 2.92/0.99  --sat_fm_prep                           false
% 2.92/0.99  --sat_fm_uc_incr                        true
% 2.92/0.99  --sat_out_model                         small
% 2.92/0.99  --sat_out_clauses                       false
% 2.92/0.99  
% 2.92/0.99  ------ QBF Options
% 2.92/0.99  
% 2.92/0.99  --qbf_mode                              false
% 2.92/0.99  --qbf_elim_univ                         false
% 2.92/0.99  --qbf_dom_inst                          none
% 2.92/0.99  --qbf_dom_pre_inst                      false
% 2.92/0.99  --qbf_sk_in                             false
% 2.92/0.99  --qbf_pred_elim                         true
% 2.92/0.99  --qbf_split                             512
% 2.92/0.99  
% 2.92/0.99  ------ BMC1 Options
% 2.92/0.99  
% 2.92/0.99  --bmc1_incremental                      false
% 2.92/0.99  --bmc1_axioms                           reachable_all
% 2.92/0.99  --bmc1_min_bound                        0
% 2.92/0.99  --bmc1_max_bound                        -1
% 2.92/0.99  --bmc1_max_bound_default                -1
% 2.92/0.99  --bmc1_symbol_reachability              true
% 2.92/0.99  --bmc1_property_lemmas                  false
% 2.92/0.99  --bmc1_k_induction                      false
% 2.92/0.99  --bmc1_non_equiv_states                 false
% 2.92/0.99  --bmc1_deadlock                         false
% 2.92/0.99  --bmc1_ucm                              false
% 2.92/0.99  --bmc1_add_unsat_core                   none
% 2.92/0.99  --bmc1_unsat_core_children              false
% 2.92/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.92/0.99  --bmc1_out_stat                         full
% 2.92/0.99  --bmc1_ground_init                      false
% 2.92/0.99  --bmc1_pre_inst_next_state              false
% 2.92/0.99  --bmc1_pre_inst_state                   false
% 2.92/0.99  --bmc1_pre_inst_reach_state             false
% 2.92/0.99  --bmc1_out_unsat_core                   false
% 2.92/0.99  --bmc1_aig_witness_out                  false
% 2.92/0.99  --bmc1_verbose                          false
% 2.92/0.99  --bmc1_dump_clauses_tptp                false
% 2.92/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.92/0.99  --bmc1_dump_file                        -
% 2.92/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.92/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.92/0.99  --bmc1_ucm_extend_mode                  1
% 2.92/0.99  --bmc1_ucm_init_mode                    2
% 2.92/0.99  --bmc1_ucm_cone_mode                    none
% 2.92/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.92/0.99  --bmc1_ucm_relax_model                  4
% 2.92/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.92/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.92/0.99  --bmc1_ucm_layered_model                none
% 2.92/0.99  --bmc1_ucm_max_lemma_size               10
% 2.92/0.99  
% 2.92/0.99  ------ AIG Options
% 2.92/0.99  
% 2.92/0.99  --aig_mode                              false
% 2.92/0.99  
% 2.92/0.99  ------ Instantiation Options
% 2.92/0.99  
% 2.92/0.99  --instantiation_flag                    true
% 2.92/0.99  --inst_sos_flag                         false
% 2.92/0.99  --inst_sos_phase                        true
% 2.92/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.92/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.92/0.99  --inst_lit_sel_side                     num_symb
% 2.92/0.99  --inst_solver_per_active                1400
% 2.92/0.99  --inst_solver_calls_frac                1.
% 2.92/0.99  --inst_passive_queue_type               priority_queues
% 2.92/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.92/0.99  --inst_passive_queues_freq              [25;2]
% 2.92/0.99  --inst_dismatching                      true
% 2.92/0.99  --inst_eager_unprocessed_to_passive     true
% 2.92/0.99  --inst_prop_sim_given                   true
% 2.92/0.99  --inst_prop_sim_new                     false
% 2.92/0.99  --inst_subs_new                         false
% 2.92/0.99  --inst_eq_res_simp                      false
% 2.92/0.99  --inst_subs_given                       false
% 2.92/0.99  --inst_orphan_elimination               true
% 2.92/0.99  --inst_learning_loop_flag               true
% 2.92/0.99  --inst_learning_start                   3000
% 2.92/0.99  --inst_learning_factor                  2
% 2.92/0.99  --inst_start_prop_sim_after_learn       3
% 2.92/0.99  --inst_sel_renew                        solver
% 2.92/0.99  --inst_lit_activity_flag                true
% 2.92/0.99  --inst_restr_to_given                   false
% 2.92/0.99  --inst_activity_threshold               500
% 2.92/0.99  --inst_out_proof                        true
% 2.92/0.99  
% 2.92/0.99  ------ Resolution Options
% 2.92/0.99  
% 2.92/0.99  --resolution_flag                       true
% 2.92/0.99  --res_lit_sel                           adaptive
% 2.92/0.99  --res_lit_sel_side                      none
% 2.92/0.99  --res_ordering                          kbo
% 2.92/0.99  --res_to_prop_solver                    active
% 2.92/0.99  --res_prop_simpl_new                    false
% 2.92/0.99  --res_prop_simpl_given                  true
% 2.92/0.99  --res_passive_queue_type                priority_queues
% 2.92/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.92/0.99  --res_passive_queues_freq               [15;5]
% 2.92/0.99  --res_forward_subs                      full
% 2.92/0.99  --res_backward_subs                     full
% 2.92/0.99  --res_forward_subs_resolution           true
% 2.92/0.99  --res_backward_subs_resolution          true
% 2.92/0.99  --res_orphan_elimination                true
% 2.92/0.99  --res_time_limit                        2.
% 2.92/0.99  --res_out_proof                         true
% 2.92/0.99  
% 2.92/0.99  ------ Superposition Options
% 2.92/0.99  
% 2.92/0.99  --superposition_flag                    true
% 2.92/0.99  --sup_passive_queue_type                priority_queues
% 2.92/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.92/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.92/0.99  --demod_completeness_check              fast
% 2.92/0.99  --demod_use_ground                      true
% 2.92/0.99  --sup_to_prop_solver                    passive
% 2.92/0.99  --sup_prop_simpl_new                    true
% 2.92/0.99  --sup_prop_simpl_given                  true
% 2.92/0.99  --sup_fun_splitting                     false
% 2.92/0.99  --sup_smt_interval                      50000
% 2.92/0.99  
% 2.92/0.99  ------ Superposition Simplification Setup
% 2.92/0.99  
% 2.92/0.99  --sup_indices_passive                   []
% 2.92/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.92/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.92/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.92/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.92/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.92/0.99  --sup_full_bw                           [BwDemod]
% 2.92/0.99  --sup_immed_triv                        [TrivRules]
% 2.92/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.92/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.92/0.99  --sup_immed_bw_main                     []
% 2.92/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.92/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.92/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.92/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.92/0.99  
% 2.92/0.99  ------ Combination Options
% 2.92/0.99  
% 2.92/0.99  --comb_res_mult                         3
% 2.92/0.99  --comb_sup_mult                         2
% 2.92/0.99  --comb_inst_mult                        10
% 2.92/0.99  
% 2.92/0.99  ------ Debug Options
% 2.92/0.99  
% 2.92/0.99  --dbg_backtrace                         false
% 2.92/0.99  --dbg_dump_prop_clauses                 false
% 2.92/0.99  --dbg_dump_prop_clauses_file            -
% 2.92/0.99  --dbg_out_stat                          false
% 2.92/0.99  ------ Parsing...
% 2.92/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.92/0.99  
% 2.92/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.92/0.99  
% 2.92/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.92/0.99  
% 2.92/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.92/0.99  ------ Proving...
% 2.92/0.99  ------ Problem Properties 
% 2.92/0.99  
% 2.92/0.99  
% 2.92/0.99  clauses                                 34
% 2.92/0.99  conjectures                             3
% 2.92/0.99  EPR                                     3
% 2.92/0.99  Horn                                    29
% 2.92/0.99  unary                                   16
% 2.92/0.99  binary                                  4
% 2.92/0.99  lits                                    75
% 2.92/0.99  lits eq                                 35
% 2.92/0.99  fd_pure                                 0
% 2.92/0.99  fd_pseudo                               0
% 2.92/0.99  fd_cond                                 2
% 2.92/0.99  fd_pseudo_cond                          4
% 2.92/0.99  AC symbols                              0
% 2.92/0.99  
% 2.92/0.99  ------ Schedule dynamic 5 is on 
% 2.92/0.99  
% 2.92/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.92/0.99  
% 2.92/0.99  
% 2.92/0.99  ------ 
% 2.92/0.99  Current options:
% 2.92/0.99  ------ 
% 2.92/0.99  
% 2.92/0.99  ------ Input Options
% 2.92/0.99  
% 2.92/0.99  --out_options                           all
% 2.92/0.99  --tptp_safe_out                         true
% 2.92/0.99  --problem_path                          ""
% 2.92/0.99  --include_path                          ""
% 2.92/0.99  --clausifier                            res/vclausify_rel
% 2.92/0.99  --clausifier_options                    --mode clausify
% 2.92/0.99  --stdin                                 false
% 2.92/0.99  --stats_out                             all
% 2.92/0.99  
% 2.92/0.99  ------ General Options
% 2.92/0.99  
% 2.92/0.99  --fof                                   false
% 2.92/0.99  --time_out_real                         305.
% 2.92/0.99  --time_out_virtual                      -1.
% 2.92/0.99  --symbol_type_check                     false
% 2.92/0.99  --clausify_out                          false
% 2.92/0.99  --sig_cnt_out                           false
% 2.92/0.99  --trig_cnt_out                          false
% 2.92/0.99  --trig_cnt_out_tolerance                1.
% 2.92/0.99  --trig_cnt_out_sk_spl                   false
% 2.92/0.99  --abstr_cl_out                          false
% 2.92/0.99  
% 2.92/0.99  ------ Global Options
% 2.92/0.99  
% 2.92/0.99  --schedule                              default
% 2.92/0.99  --add_important_lit                     false
% 2.92/0.99  --prop_solver_per_cl                    1000
% 2.92/0.99  --min_unsat_core                        false
% 2.92/0.99  --soft_assumptions                      false
% 2.92/0.99  --soft_lemma_size                       3
% 2.92/0.99  --prop_impl_unit_size                   0
% 2.92/0.99  --prop_impl_unit                        []
% 2.92/0.99  --share_sel_clauses                     true
% 2.92/0.99  --reset_solvers                         false
% 2.92/0.99  --bc_imp_inh                            [conj_cone]
% 2.92/0.99  --conj_cone_tolerance                   3.
% 2.92/0.99  --extra_neg_conj                        none
% 2.92/0.99  --large_theory_mode                     true
% 2.92/0.99  --prolific_symb_bound                   200
% 2.92/0.99  --lt_threshold                          2000
% 2.92/0.99  --clause_weak_htbl                      true
% 2.92/0.99  --gc_record_bc_elim                     false
% 2.92/0.99  
% 2.92/0.99  ------ Preprocessing Options
% 2.92/0.99  
% 2.92/0.99  --preprocessing_flag                    true
% 2.92/0.99  --time_out_prep_mult                    0.1
% 2.92/0.99  --splitting_mode                        input
% 2.92/0.99  --splitting_grd                         true
% 2.92/0.99  --splitting_cvd                         false
% 2.92/0.99  --splitting_cvd_svl                     false
% 2.92/0.99  --splitting_nvd                         32
% 2.92/0.99  --sub_typing                            true
% 2.92/0.99  --prep_gs_sim                           true
% 2.92/0.99  --prep_unflatten                        true
% 2.92/0.99  --prep_res_sim                          true
% 2.92/0.99  --prep_upred                            true
% 2.92/0.99  --prep_sem_filter                       exhaustive
% 2.92/0.99  --prep_sem_filter_out                   false
% 2.92/0.99  --pred_elim                             true
% 2.92/0.99  --res_sim_input                         true
% 2.92/0.99  --eq_ax_congr_red                       true
% 2.92/0.99  --pure_diseq_elim                       true
% 2.92/0.99  --brand_transform                       false
% 2.92/0.99  --non_eq_to_eq                          false
% 2.92/0.99  --prep_def_merge                        true
% 2.92/0.99  --prep_def_merge_prop_impl              false
% 2.92/0.99  --prep_def_merge_mbd                    true
% 2.92/0.99  --prep_def_merge_tr_red                 false
% 2.92/0.99  --prep_def_merge_tr_cl                  false
% 2.92/0.99  --smt_preprocessing                     true
% 2.92/0.99  --smt_ac_axioms                         fast
% 2.92/0.99  --preprocessed_out                      false
% 2.92/0.99  --preprocessed_stats                    false
% 2.92/0.99  
% 2.92/0.99  ------ Abstraction refinement Options
% 2.92/0.99  
% 2.92/0.99  --abstr_ref                             []
% 2.92/0.99  --abstr_ref_prep                        false
% 2.92/0.99  --abstr_ref_until_sat                   false
% 2.92/0.99  --abstr_ref_sig_restrict                funpre
% 2.92/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.92/0.99  --abstr_ref_under                       []
% 2.92/0.99  
% 2.92/0.99  ------ SAT Options
% 2.92/0.99  
% 2.92/0.99  --sat_mode                              false
% 2.92/0.99  --sat_fm_restart_options                ""
% 2.92/0.99  --sat_gr_def                            false
% 2.92/0.99  --sat_epr_types                         true
% 2.92/0.99  --sat_non_cyclic_types                  false
% 2.92/0.99  --sat_finite_models                     false
% 2.92/0.99  --sat_fm_lemmas                         false
% 2.92/0.99  --sat_fm_prep                           false
% 2.92/0.99  --sat_fm_uc_incr                        true
% 2.92/0.99  --sat_out_model                         small
% 2.92/0.99  --sat_out_clauses                       false
% 2.92/0.99  
% 2.92/0.99  ------ QBF Options
% 2.92/0.99  
% 2.92/0.99  --qbf_mode                              false
% 2.92/0.99  --qbf_elim_univ                         false
% 2.92/0.99  --qbf_dom_inst                          none
% 2.92/0.99  --qbf_dom_pre_inst                      false
% 2.92/0.99  --qbf_sk_in                             false
% 2.92/0.99  --qbf_pred_elim                         true
% 2.92/0.99  --qbf_split                             512
% 2.92/0.99  
% 2.92/0.99  ------ BMC1 Options
% 2.92/0.99  
% 2.92/0.99  --bmc1_incremental                      false
% 2.92/0.99  --bmc1_axioms                           reachable_all
% 2.92/0.99  --bmc1_min_bound                        0
% 2.92/0.99  --bmc1_max_bound                        -1
% 2.92/0.99  --bmc1_max_bound_default                -1
% 2.92/0.99  --bmc1_symbol_reachability              true
% 2.92/0.99  --bmc1_property_lemmas                  false
% 2.92/0.99  --bmc1_k_induction                      false
% 2.92/0.99  --bmc1_non_equiv_states                 false
% 2.92/0.99  --bmc1_deadlock                         false
% 2.92/0.99  --bmc1_ucm                              false
% 2.92/0.99  --bmc1_add_unsat_core                   none
% 2.92/0.99  --bmc1_unsat_core_children              false
% 2.92/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.92/0.99  --bmc1_out_stat                         full
% 2.92/0.99  --bmc1_ground_init                      false
% 2.92/0.99  --bmc1_pre_inst_next_state              false
% 2.92/0.99  --bmc1_pre_inst_state                   false
% 2.92/0.99  --bmc1_pre_inst_reach_state             false
% 2.92/0.99  --bmc1_out_unsat_core                   false
% 2.92/0.99  --bmc1_aig_witness_out                  false
% 2.92/0.99  --bmc1_verbose                          false
% 2.92/0.99  --bmc1_dump_clauses_tptp                false
% 2.92/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.92/0.99  --bmc1_dump_file                        -
% 2.92/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.92/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.92/0.99  --bmc1_ucm_extend_mode                  1
% 2.92/0.99  --bmc1_ucm_init_mode                    2
% 2.92/0.99  --bmc1_ucm_cone_mode                    none
% 2.92/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.92/0.99  --bmc1_ucm_relax_model                  4
% 2.92/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.92/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.92/0.99  --bmc1_ucm_layered_model                none
% 2.92/0.99  --bmc1_ucm_max_lemma_size               10
% 2.92/0.99  
% 2.92/0.99  ------ AIG Options
% 2.92/0.99  
% 2.92/0.99  --aig_mode                              false
% 2.92/0.99  
% 2.92/0.99  ------ Instantiation Options
% 2.92/0.99  
% 2.92/0.99  --instantiation_flag                    true
% 2.92/0.99  --inst_sos_flag                         false
% 2.92/0.99  --inst_sos_phase                        true
% 2.92/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.92/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.92/0.99  --inst_lit_sel_side                     none
% 2.92/0.99  --inst_solver_per_active                1400
% 2.92/0.99  --inst_solver_calls_frac                1.
% 2.92/0.99  --inst_passive_queue_type               priority_queues
% 2.92/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.92/0.99  --inst_passive_queues_freq              [25;2]
% 2.92/0.99  --inst_dismatching                      true
% 2.92/0.99  --inst_eager_unprocessed_to_passive     true
% 2.92/0.99  --inst_prop_sim_given                   true
% 2.92/0.99  --inst_prop_sim_new                     false
% 2.92/0.99  --inst_subs_new                         false
% 2.92/0.99  --inst_eq_res_simp                      false
% 2.92/0.99  --inst_subs_given                       false
% 2.92/0.99  --inst_orphan_elimination               true
% 2.92/0.99  --inst_learning_loop_flag               true
% 2.92/0.99  --inst_learning_start                   3000
% 2.92/0.99  --inst_learning_factor                  2
% 2.92/0.99  --inst_start_prop_sim_after_learn       3
% 2.92/0.99  --inst_sel_renew                        solver
% 2.92/0.99  --inst_lit_activity_flag                true
% 2.92/0.99  --inst_restr_to_given                   false
% 2.92/0.99  --inst_activity_threshold               500
% 2.92/0.99  --inst_out_proof                        true
% 2.92/0.99  
% 2.92/0.99  ------ Resolution Options
% 2.92/0.99  
% 2.92/0.99  --resolution_flag                       false
% 2.92/0.99  --res_lit_sel                           adaptive
% 2.92/0.99  --res_lit_sel_side                      none
% 2.92/0.99  --res_ordering                          kbo
% 2.92/0.99  --res_to_prop_solver                    active
% 2.92/0.99  --res_prop_simpl_new                    false
% 2.92/0.99  --res_prop_simpl_given                  true
% 2.92/0.99  --res_passive_queue_type                priority_queues
% 2.92/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.92/0.99  --res_passive_queues_freq               [15;5]
% 2.92/0.99  --res_forward_subs                      full
% 2.92/0.99  --res_backward_subs                     full
% 2.92/0.99  --res_forward_subs_resolution           true
% 2.92/0.99  --res_backward_subs_resolution          true
% 2.92/0.99  --res_orphan_elimination                true
% 2.92/0.99  --res_time_limit                        2.
% 2.92/0.99  --res_out_proof                         true
% 2.92/0.99  
% 2.92/0.99  ------ Superposition Options
% 2.92/0.99  
% 2.92/0.99  --superposition_flag                    true
% 2.92/0.99  --sup_passive_queue_type                priority_queues
% 2.92/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.92/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.92/0.99  --demod_completeness_check              fast
% 2.92/0.99  --demod_use_ground                      true
% 2.92/0.99  --sup_to_prop_solver                    passive
% 2.92/0.99  --sup_prop_simpl_new                    true
% 2.92/0.99  --sup_prop_simpl_given                  true
% 2.92/0.99  --sup_fun_splitting                     false
% 2.92/0.99  --sup_smt_interval                      50000
% 2.92/0.99  
% 2.92/0.99  ------ Superposition Simplification Setup
% 2.92/0.99  
% 2.92/0.99  --sup_indices_passive                   []
% 2.92/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.92/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.92/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.92/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.92/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.92/0.99  --sup_full_bw                           [BwDemod]
% 2.92/0.99  --sup_immed_triv                        [TrivRules]
% 2.92/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.92/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.92/0.99  --sup_immed_bw_main                     []
% 2.92/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.92/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.92/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.92/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.92/0.99  
% 2.92/0.99  ------ Combination Options
% 2.92/0.99  
% 2.92/0.99  --comb_res_mult                         3
% 2.92/0.99  --comb_sup_mult                         2
% 2.92/0.99  --comb_inst_mult                        10
% 2.92/0.99  
% 2.92/0.99  ------ Debug Options
% 2.92/0.99  
% 2.92/0.99  --dbg_backtrace                         false
% 2.92/0.99  --dbg_dump_prop_clauses                 false
% 2.92/0.99  --dbg_dump_prop_clauses_file            -
% 2.92/0.99  --dbg_out_stat                          false
% 2.92/0.99  
% 2.92/0.99  
% 2.92/0.99  
% 2.92/0.99  
% 2.92/0.99  ------ Proving...
% 2.92/0.99  
% 2.92/0.99  
% 2.92/0.99  % SZS status Theorem for theBenchmark.p
% 2.92/0.99  
% 2.92/0.99   Resolution empty clause
% 2.92/0.99  
% 2.92/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.92/0.99  
% 2.92/0.99  fof(f2,axiom,(
% 2.92/0.99    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 2.92/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f38,plain,(
% 2.92/1.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.92/1.00    inference(nnf_transformation,[],[f2])).
% 2.92/1.00  
% 2.92/1.00  fof(f39,plain,(
% 2.92/1.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.92/1.00    inference(flattening,[],[f38])).
% 2.92/1.00  
% 2.92/1.00  fof(f40,plain,(
% 2.92/1.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.92/1.00    inference(rectify,[],[f39])).
% 2.92/1.00  
% 2.92/1.00  fof(f41,plain,(
% 2.92/1.00    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2))))),
% 2.92/1.00    introduced(choice_axiom,[])).
% 2.92/1.00  
% 2.92/1.00  fof(f42,plain,(
% 2.92/1.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.92/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).
% 2.92/1.00  
% 2.92/1.00  fof(f57,plain,(
% 2.92/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 2.92/1.00    inference(cnf_transformation,[],[f42])).
% 2.92/1.00  
% 2.92/1.00  fof(f4,axiom,(
% 2.92/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.92/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f62,plain,(
% 2.92/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.92/1.00    inference(cnf_transformation,[],[f4])).
% 2.92/1.00  
% 2.92/1.00  fof(f5,axiom,(
% 2.92/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.92/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f63,plain,(
% 2.92/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.92/1.00    inference(cnf_transformation,[],[f5])).
% 2.92/1.00  
% 2.92/1.00  fof(f98,plain,(
% 2.92/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.92/1.00    inference(definition_unfolding,[],[f62,f63])).
% 2.92/1.00  
% 2.92/1.00  fof(f103,plain,(
% 2.92/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 2.92/1.00    inference(definition_unfolding,[],[f57,f98])).
% 2.92/1.00  
% 2.92/1.00  fof(f119,plain,(
% 2.92/1.00    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X4) != X2) )),
% 2.92/1.00    inference(equality_resolution,[],[f103])).
% 2.92/1.00  
% 2.92/1.00  fof(f120,plain,(
% 2.92/1.00    ( ! [X4,X0] : (r2_hidden(X4,k2_enumset1(X0,X0,X0,X4))) )),
% 2.92/1.00    inference(equality_resolution,[],[f119])).
% 2.92/1.00  
% 2.92/1.00  fof(f18,conjecture,(
% 2.92/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 2.92/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f19,negated_conjecture,(
% 2.92/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 2.92/1.00    inference(negated_conjecture,[],[f18])).
% 2.92/1.00  
% 2.92/1.00  fof(f36,plain,(
% 2.92/1.00    ? [X0,X1,X2] : ((k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 2.92/1.00    inference(ennf_transformation,[],[f19])).
% 2.92/1.00  
% 2.92/1.00  fof(f37,plain,(
% 2.92/1.00    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 2.92/1.00    inference(flattening,[],[f36])).
% 2.92/1.00  
% 2.92/1.00  fof(f52,plain,(
% 2.92/1.00    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_tarski(k1_funct_1(sK5,sK3)) != k2_relset_1(k1_tarski(sK3),sK4,sK5) & k1_xboole_0 != sK4 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4))) & v1_funct_2(sK5,k1_tarski(sK3),sK4) & v1_funct_1(sK5))),
% 2.92/1.00    introduced(choice_axiom,[])).
% 2.92/1.00  
% 2.92/1.00  fof(f53,plain,(
% 2.92/1.00    k1_tarski(k1_funct_1(sK5,sK3)) != k2_relset_1(k1_tarski(sK3),sK4,sK5) & k1_xboole_0 != sK4 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4))) & v1_funct_2(sK5,k1_tarski(sK3),sK4) & v1_funct_1(sK5)),
% 2.92/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f37,f52])).
% 2.92/1.00  
% 2.92/1.00  fof(f95,plain,(
% 2.92/1.00    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4)))),
% 2.92/1.00    inference(cnf_transformation,[],[f53])).
% 2.92/1.00  
% 2.92/1.00  fof(f3,axiom,(
% 2.92/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.92/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f61,plain,(
% 2.92/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.92/1.00    inference(cnf_transformation,[],[f3])).
% 2.92/1.00  
% 2.92/1.00  fof(f99,plain,(
% 2.92/1.00    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.92/1.00    inference(definition_unfolding,[],[f61,f98])).
% 2.92/1.00  
% 2.92/1.00  fof(f117,plain,(
% 2.92/1.00    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))),
% 2.92/1.00    inference(definition_unfolding,[],[f95,f99])).
% 2.92/1.00  
% 2.92/1.00  fof(f14,axiom,(
% 2.92/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.92/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f20,plain,(
% 2.92/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.92/1.00    inference(pure_predicate_removal,[],[f14])).
% 2.92/1.00  
% 2.92/1.00  fof(f31,plain,(
% 2.92/1.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.92/1.00    inference(ennf_transformation,[],[f20])).
% 2.92/1.00  
% 2.92/1.00  fof(f82,plain,(
% 2.92/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.92/1.00    inference(cnf_transformation,[],[f31])).
% 2.92/1.00  
% 2.92/1.00  fof(f9,axiom,(
% 2.92/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.92/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f24,plain,(
% 2.92/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.92/1.00    inference(ennf_transformation,[],[f9])).
% 2.92/1.00  
% 2.92/1.00  fof(f45,plain,(
% 2.92/1.00    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.92/1.00    inference(nnf_transformation,[],[f24])).
% 2.92/1.00  
% 2.92/1.00  fof(f75,plain,(
% 2.92/1.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.92/1.00    inference(cnf_transformation,[],[f45])).
% 2.92/1.00  
% 2.92/1.00  fof(f13,axiom,(
% 2.92/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.92/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f30,plain,(
% 2.92/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.92/1.00    inference(ennf_transformation,[],[f13])).
% 2.92/1.00  
% 2.92/1.00  fof(f81,plain,(
% 2.92/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.92/1.00    inference(cnf_transformation,[],[f30])).
% 2.92/1.00  
% 2.92/1.00  fof(f6,axiom,(
% 2.92/1.00    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> ~(k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3))),
% 2.92/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f21,plain,(
% 2.92/1.00    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3))),
% 2.92/1.00    inference(ennf_transformation,[],[f6])).
% 2.92/1.00  
% 2.92/1.00  fof(f43,plain,(
% 2.92/1.00    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & ((k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3) | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 2.92/1.00    inference(nnf_transformation,[],[f21])).
% 2.92/1.00  
% 2.92/1.00  fof(f44,plain,(
% 2.92/1.00    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 2.92/1.00    inference(flattening,[],[f43])).
% 2.92/1.00  
% 2.92/1.00  fof(f64,plain,(
% 2.92/1.00    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))) )),
% 2.92/1.00    inference(cnf_transformation,[],[f44])).
% 2.92/1.00  
% 2.92/1.00  fof(f114,plain,(
% 2.92/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X0,X1,X2) = X3 | k2_enumset1(X0,X0,X0,X2) = X3 | k2_enumset1(X1,X1,X1,X2) = X3 | k2_enumset1(X0,X0,X0,X1) = X3 | k2_enumset1(X2,X2,X2,X2) = X3 | k2_enumset1(X1,X1,X1,X1) = X3 | k2_enumset1(X0,X0,X0,X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k2_enumset1(X0,X0,X1,X2))) )),
% 2.92/1.00    inference(definition_unfolding,[],[f64,f63,f98,f98,f98,f99,f99,f99,f63])).
% 2.92/1.00  
% 2.92/1.00  fof(f97,plain,(
% 2.92/1.00    k1_tarski(k1_funct_1(sK5,sK3)) != k2_relset_1(k1_tarski(sK3),sK4,sK5)),
% 2.92/1.00    inference(cnf_transformation,[],[f53])).
% 2.92/1.00  
% 2.92/1.00  fof(f116,plain,(
% 2.92/1.00    k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5)),
% 2.92/1.00    inference(definition_unfolding,[],[f97,f99,f99])).
% 2.92/1.00  
% 2.92/1.00  fof(f15,axiom,(
% 2.92/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.92/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f32,plain,(
% 2.92/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.92/1.00    inference(ennf_transformation,[],[f15])).
% 2.92/1.00  
% 2.92/1.00  fof(f83,plain,(
% 2.92/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.92/1.00    inference(cnf_transformation,[],[f32])).
% 2.92/1.00  
% 2.92/1.00  fof(f11,axiom,(
% 2.92/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 2.92/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f27,plain,(
% 2.92/1.00    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.92/1.00    inference(ennf_transformation,[],[f11])).
% 2.92/1.00  
% 2.92/1.00  fof(f28,plain,(
% 2.92/1.00    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.92/1.00    inference(flattening,[],[f27])).
% 2.92/1.00  
% 2.92/1.00  fof(f79,plain,(
% 2.92/1.00    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.92/1.00    inference(cnf_transformation,[],[f28])).
% 2.92/1.00  
% 2.92/1.00  fof(f115,plain,(
% 2.92/1.00    ( ! [X0,X1] : (k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1) | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.92/1.00    inference(definition_unfolding,[],[f79,f99,f99])).
% 2.92/1.00  
% 2.92/1.00  fof(f93,plain,(
% 2.92/1.00    v1_funct_1(sK5)),
% 2.92/1.00    inference(cnf_transformation,[],[f53])).
% 2.92/1.00  
% 2.92/1.00  fof(f10,axiom,(
% 2.92/1.00    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 2.92/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f25,plain,(
% 2.92/1.00    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.92/1.00    inference(ennf_transformation,[],[f10])).
% 2.92/1.00  
% 2.92/1.00  fof(f26,plain,(
% 2.92/1.00    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.92/1.00    inference(flattening,[],[f25])).
% 2.92/1.00  
% 2.92/1.00  fof(f77,plain,(
% 2.92/1.00    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.92/1.00    inference(cnf_transformation,[],[f26])).
% 2.92/1.00  
% 2.92/1.00  fof(f17,axiom,(
% 2.92/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.92/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f34,plain,(
% 2.92/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.92/1.00    inference(ennf_transformation,[],[f17])).
% 2.92/1.00  
% 2.92/1.00  fof(f35,plain,(
% 2.92/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.92/1.00    inference(flattening,[],[f34])).
% 2.92/1.00  
% 2.92/1.00  fof(f51,plain,(
% 2.92/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.92/1.00    inference(nnf_transformation,[],[f35])).
% 2.92/1.00  
% 2.92/1.00  fof(f87,plain,(
% 2.92/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.92/1.00    inference(cnf_transformation,[],[f51])).
% 2.92/1.00  
% 2.92/1.00  fof(f94,plain,(
% 2.92/1.00    v1_funct_2(sK5,k1_tarski(sK3),sK4)),
% 2.92/1.00    inference(cnf_transformation,[],[f53])).
% 2.92/1.00  
% 2.92/1.00  fof(f118,plain,(
% 2.92/1.00    v1_funct_2(sK5,k2_enumset1(sK3,sK3,sK3,sK3),sK4)),
% 2.92/1.00    inference(definition_unfolding,[],[f94,f99])).
% 2.92/1.00  
% 2.92/1.00  fof(f96,plain,(
% 2.92/1.00    k1_xboole_0 != sK4),
% 2.92/1.00    inference(cnf_transformation,[],[f53])).
% 2.92/1.00  
% 2.92/1.00  fof(f16,axiom,(
% 2.92/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 2.92/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f33,plain,(
% 2.92/1.00    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.92/1.00    inference(ennf_transformation,[],[f16])).
% 2.92/1.00  
% 2.92/1.00  fof(f46,plain,(
% 2.92/1.00    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.92/1.00    inference(nnf_transformation,[],[f33])).
% 2.92/1.00  
% 2.92/1.00  fof(f47,plain,(
% 2.92/1.00    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.92/1.00    inference(rectify,[],[f46])).
% 2.92/1.00  
% 2.92/1.00  fof(f49,plain,(
% 2.92/1.00    ! [X2,X1] : (? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)) => (! [X6] : ~r2_hidden(k4_tarski(sK2(X1,X2),X6),X2) & r2_hidden(sK2(X1,X2),X1)))),
% 2.92/1.00    introduced(choice_axiom,[])).
% 2.92/1.00  
% 2.92/1.00  fof(f48,plain,(
% 2.92/1.00    ! [X3,X2] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) => r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2))),
% 2.92/1.00    introduced(choice_axiom,[])).
% 2.92/1.00  
% 2.92/1.00  fof(f50,plain,(
% 2.92/1.00    ! [X0,X1,X2] : (((! [X3] : (r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | (! [X6] : ~r2_hidden(k4_tarski(sK2(X1,X2),X6),X2) & r2_hidden(sK2(X1,X2),X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.92/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f47,f49,f48])).
% 2.92/1.00  
% 2.92/1.00  fof(f86,plain,(
% 2.92/1.00    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2) | ~r2_hidden(X3,X1) | k1_relset_1(X1,X0,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 2.92/1.00    inference(cnf_transformation,[],[f50])).
% 2.92/1.00  
% 2.92/1.00  fof(f8,axiom,(
% 2.92/1.00    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.92/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f22,plain,(
% 2.92/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.92/1.00    inference(ennf_transformation,[],[f8])).
% 2.92/1.00  
% 2.92/1.00  fof(f23,plain,(
% 2.92/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.92/1.00    inference(flattening,[],[f22])).
% 2.92/1.00  
% 2.92/1.00  fof(f74,plain,(
% 2.92/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.92/1.00    inference(cnf_transformation,[],[f23])).
% 2.92/1.00  
% 2.92/1.00  fof(f1,axiom,(
% 2.92/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.92/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f54,plain,(
% 2.92/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.92/1.00    inference(cnf_transformation,[],[f1])).
% 2.92/1.00  
% 2.92/1.00  fof(f12,axiom,(
% 2.92/1.00    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.92/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f29,plain,(
% 2.92/1.00    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.92/1.00    inference(ennf_transformation,[],[f12])).
% 2.92/1.00  
% 2.92/1.00  fof(f80,plain,(
% 2.92/1.00    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.92/1.00    inference(cnf_transformation,[],[f29])).
% 2.92/1.00  
% 2.92/1.00  cnf(c_4,plain,
% 2.92/1.00      ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) ),
% 2.92/1.00      inference(cnf_transformation,[],[f120]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2102,plain,
% 2.92/1.00      ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) = iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_38,negated_conjecture,
% 2.92/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) ),
% 2.92/1.00      inference(cnf_transformation,[],[f117]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2080,plain,
% 2.92/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) = iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_25,plain,
% 2.92/1.00      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.92/1.00      inference(cnf_transformation,[],[f82]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_19,plain,
% 2.92/1.00      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 2.92/1.00      inference(cnf_transformation,[],[f75]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_447,plain,
% 2.92/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.92/1.00      | r1_tarski(k1_relat_1(X0),X1)
% 2.92/1.00      | ~ v1_relat_1(X0) ),
% 2.92/1.00      inference(resolution,[status(thm)],[c_25,c_19]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_24,plain,
% 2.92/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.92/1.00      inference(cnf_transformation,[],[f81]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_451,plain,
% 2.92/1.00      ( r1_tarski(k1_relat_1(X0),X1)
% 2.92/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.92/1.00      inference(global_propositional_subsumption,[status(thm)],[c_447,c_24]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_452,plain,
% 2.92/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.92/1.00      | r1_tarski(k1_relat_1(X0),X1) ),
% 2.92/1.00      inference(renaming,[status(thm)],[c_451]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2078,plain,
% 2.92/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.92/1.00      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_452]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2449,plain,
% 2.92/1.00      ( r1_tarski(k1_relat_1(sK5),k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top ),
% 2.92/1.00      inference(superposition,[status(thm)],[c_2080,c_2078]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_15,plain,
% 2.92/1.00      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X2,X3))
% 2.92/1.00      | k2_enumset1(X1,X1,X2,X3) = X0
% 2.92/1.00      | k2_enumset1(X1,X1,X1,X3) = X0
% 2.92/1.00      | k2_enumset1(X2,X2,X2,X3) = X0
% 2.92/1.00      | k2_enumset1(X1,X1,X1,X2) = X0
% 2.92/1.00      | k2_enumset1(X3,X3,X3,X3) = X0
% 2.92/1.00      | k2_enumset1(X2,X2,X2,X2) = X0
% 2.92/1.00      | k2_enumset1(X1,X1,X1,X1) = X0
% 2.92/1.00      | k1_xboole_0 = X0 ),
% 2.92/1.00      inference(cnf_transformation,[],[f114]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2091,plain,
% 2.92/1.00      ( k2_enumset1(X0,X0,X1,X2) = X3
% 2.92/1.00      | k2_enumset1(X0,X0,X0,X2) = X3
% 2.92/1.00      | k2_enumset1(X1,X1,X1,X2) = X3
% 2.92/1.00      | k2_enumset1(X0,X0,X0,X1) = X3
% 2.92/1.00      | k2_enumset1(X2,X2,X2,X2) = X3
% 2.92/1.00      | k2_enumset1(X1,X1,X1,X1) = X3
% 2.92/1.00      | k2_enumset1(X0,X0,X0,X0) = X3
% 2.92/1.00      | k1_xboole_0 = X3
% 2.92/1.00      | r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) != iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_3728,plain,
% 2.92/1.00      ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_relat_1(sK5)
% 2.92/1.00      | k1_relat_1(sK5) = k1_xboole_0 ),
% 2.92/1.00      inference(superposition,[status(thm)],[c_2449,c_2091]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_36,negated_conjecture,
% 2.92/1.00      ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) ),
% 2.92/1.00      inference(cnf_transformation,[],[f116]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2336,plain,
% 2.92/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))
% 2.92/1.00      | v1_relat_1(sK5) ),
% 2.92/1.00      inference(instantiation,[status(thm)],[c_24]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_26,plain,
% 2.92/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.92/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.92/1.00      inference(cnf_transformation,[],[f83]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2362,plain,
% 2.92/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))
% 2.92/1.00      | k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_relat_1(sK5) ),
% 2.92/1.00      inference(instantiation,[status(thm)],[c_26]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_1553,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2355,plain,
% 2.92/1.00      ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != X0
% 2.92/1.00      | k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) = k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5)
% 2.92/1.00      | k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) != X0 ),
% 2.92/1.00      inference(instantiation,[status(thm)],[c_1553]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2471,plain,
% 2.92/1.00      ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) = k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5)
% 2.92/1.00      | k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relat_1(sK5)
% 2.92/1.00      | k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) != k2_relat_1(sK5) ),
% 2.92/1.00      inference(instantiation,[status(thm)],[c_2355]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_22,plain,
% 2.92/1.00      ( ~ v1_funct_1(X0)
% 2.92/1.00      | ~ v1_relat_1(X0)
% 2.92/1.00      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 2.92/1.00      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
% 2.92/1.00      inference(cnf_transformation,[],[f115]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_40,negated_conjecture,
% 2.92/1.00      ( v1_funct_1(sK5) ),
% 2.92/1.00      inference(cnf_transformation,[],[f93]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_428,plain,
% 2.92/1.00      ( ~ v1_relat_1(X0)
% 2.92/1.00      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 2.92/1.00      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
% 2.92/1.00      | sK5 != X0 ),
% 2.92/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_40]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_429,plain,
% 2.92/1.00      ( ~ v1_relat_1(sK5)
% 2.92/1.00      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5)
% 2.92/1.00      | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5) ),
% 2.92/1.00      inference(unflattening,[status(thm)],[c_428]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2762,plain,
% 2.92/1.00      ( ~ v1_relat_1(sK5)
% 2.92/1.00      | k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) = k2_relat_1(sK5)
% 2.92/1.00      | k2_enumset1(sK3,sK3,sK3,sK3) != k1_relat_1(sK5) ),
% 2.92/1.00      inference(instantiation,[status(thm)],[c_429]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_4233,plain,
% 2.92/1.00      ( k1_relat_1(sK5) = k1_xboole_0 ),
% 2.92/1.00      inference(global_propositional_subsumption,
% 2.92/1.00                [status(thm)],
% 2.92/1.00                [c_3728,c_38,c_36,c_2336,c_2362,c_2471,c_2762]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_21,plain,
% 2.92/1.00      ( ~ v1_relat_1(X0) | k1_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 2.92/1.00      inference(cnf_transformation,[],[f77]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2087,plain,
% 2.92/1.00      ( k1_relat_1(X0) != k1_xboole_0
% 2.92/1.00      | k1_xboole_0 = X0
% 2.92/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_4244,plain,
% 2.92/1.00      ( sK5 = k1_xboole_0 | v1_relat_1(sK5) != iProver_top ),
% 2.92/1.00      inference(superposition,[status(thm)],[c_4233,c_2087]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2514,plain,
% 2.92/1.00      ( ~ v1_relat_1(sK5)
% 2.92/1.00      | k1_relat_1(sK5) != k1_xboole_0
% 2.92/1.00      | k1_xboole_0 = sK5 ),
% 2.92/1.00      inference(instantiation,[status(thm)],[c_21]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_1552,plain,( X0 = X0 ),theory(equality) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2529,plain,
% 2.92/1.00      ( sK5 = sK5 ),
% 2.92/1.00      inference(instantiation,[status(thm)],[c_1552]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2720,plain,
% 2.92/1.00      ( X0 != X1 | sK5 != X1 | sK5 = X0 ),
% 2.92/1.00      inference(instantiation,[status(thm)],[c_1553]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_3831,plain,
% 2.92/1.00      ( X0 != sK5 | sK5 = X0 | sK5 != sK5 ),
% 2.92/1.00      inference(instantiation,[status(thm)],[c_2720]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_3832,plain,
% 2.92/1.00      ( sK5 != sK5 | sK5 = k1_xboole_0 | k1_xboole_0 != sK5 ),
% 2.92/1.00      inference(instantiation,[status(thm)],[c_3831]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_4644,plain,
% 2.92/1.00      ( sK5 = k1_xboole_0 ),
% 2.92/1.00      inference(global_propositional_subsumption,
% 2.92/1.00                [status(thm)],
% 2.92/1.00                [c_4244,c_38,c_36,c_2336,c_2362,c_2471,c_2514,c_2529,c_2762,
% 2.92/1.00                 c_3728,c_3832]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_35,plain,
% 2.92/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.92/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.92/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.92/1.00      | k1_xboole_0 = X2 ),
% 2.92/1.00      inference(cnf_transformation,[],[f87]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_39,negated_conjecture,
% 2.92/1.00      ( v1_funct_2(sK5,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
% 2.92/1.00      inference(cnf_transformation,[],[f118]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_565,plain,
% 2.92/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.92/1.00      | k2_enumset1(sK3,sK3,sK3,sK3) != X1
% 2.92/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.92/1.00      | sK4 != X2
% 2.92/1.00      | sK5 != X0
% 2.92/1.00      | k1_xboole_0 = X2 ),
% 2.92/1.00      inference(resolution_lifted,[status(thm)],[c_35,c_39]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_566,plain,
% 2.92/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))
% 2.92/1.00      | k1_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_enumset1(sK3,sK3,sK3,sK3)
% 2.92/1.00      | k1_xboole_0 = sK4 ),
% 2.92/1.00      inference(unflattening,[status(thm)],[c_565]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_37,negated_conjecture,
% 2.92/1.00      ( k1_xboole_0 != sK4 ),
% 2.92/1.00      inference(cnf_transformation,[],[f96]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_568,plain,
% 2.92/1.00      ( k1_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 2.92/1.00      inference(global_propositional_subsumption,
% 2.92/1.00                [status(thm)],
% 2.92/1.00                [c_566,c_38,c_37]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_4654,plain,
% 2.92/1.00      ( k1_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0) = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 2.92/1.00      inference(demodulation,[status(thm)],[c_4644,c_568]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_27,plain,
% 2.92/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.92/1.00      | ~ r2_hidden(X3,X1)
% 2.92/1.00      | r2_hidden(k4_tarski(X3,sK1(X0,X3)),X0)
% 2.92/1.00      | k1_relset_1(X1,X2,X0) != X1 ),
% 2.92/1.00      inference(cnf_transformation,[],[f86]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2083,plain,
% 2.92/1.00      ( k1_relset_1(X0,X1,X2) != X0
% 2.92/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.92/1.00      | r2_hidden(X3,X0) != iProver_top
% 2.92/1.00      | r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2) = iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_5113,plain,
% 2.92/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) != iProver_top
% 2.92/1.00      | r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top
% 2.92/1.00      | r2_hidden(k4_tarski(X0,sK1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top ),
% 2.92/1.00      inference(superposition,[status(thm)],[c_4654,c_2083]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_43,plain,
% 2.92/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) = iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2797,plain,
% 2.92/1.00      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) = k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) ),
% 2.92/1.00      inference(instantiation,[status(thm)],[c_1552]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_1558,plain,
% 2.92/1.00      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.92/1.00      theory(equality) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2396,plain,
% 2.92/1.00      ( m1_subset_1(X0,X1)
% 2.92/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))
% 2.92/1.00      | X1 != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))
% 2.92/1.00      | X0 != sK5 ),
% 2.92/1.00      inference(instantiation,[status(thm)],[c_1558]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_4815,plain,
% 2.92/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))
% 2.92/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))
% 2.92/1.00      | X0 != sK5
% 2.92/1.00      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) ),
% 2.92/1.00      inference(instantiation,[status(thm)],[c_2396]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_4816,plain,
% 2.92/1.00      ( X0 != sK5
% 2.92/1.00      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))
% 2.92/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) = iProver_top
% 2.92/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) != iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_4815]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_4818,plain,
% 2.92/1.00      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))
% 2.92/1.00      | k1_xboole_0 != sK5
% 2.92/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) != iProver_top
% 2.92/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) = iProver_top ),
% 2.92/1.00      inference(instantiation,[status(thm)],[c_4816]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_5304,plain,
% 2.92/1.00      ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top
% 2.92/1.00      | r2_hidden(k4_tarski(X0,sK1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top ),
% 2.92/1.00      inference(global_propositional_subsumption,
% 2.92/1.00                [status(thm)],
% 2.92/1.00                [c_5113,c_38,c_43,c_36,c_2336,c_2362,c_2471,c_2514,c_2762,
% 2.92/1.00                 c_2797,c_3728,c_4818]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_17,plain,
% 2.92/1.00      ( m1_subset_1(X0,X1)
% 2.92/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.92/1.00      | ~ r2_hidden(X0,X2) ),
% 2.92/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2089,plain,
% 2.92/1.00      ( m1_subset_1(X0,X1) = iProver_top
% 2.92/1.00      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 2.92/1.00      | r2_hidden(X0,X2) != iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_3531,plain,
% 2.92/1.00      ( m1_subset_1(X0,k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) = iProver_top
% 2.92/1.00      | r2_hidden(X0,sK5) != iProver_top ),
% 2.92/1.00      inference(superposition,[status(thm)],[c_2080,c_2089]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_4649,plain,
% 2.92/1.00      ( m1_subset_1(X0,k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) = iProver_top
% 2.92/1.00      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.92/1.00      inference(demodulation,[status(thm)],[c_4644,c_3531]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_0,plain,
% 2.92/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 2.92/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_23,plain,
% 2.92/1.00      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 2.92/1.00      inference(cnf_transformation,[],[f80]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_585,plain,
% 2.92/1.00      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 2.92/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_23]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_586,plain,
% 2.92/1.00      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 2.92/1.00      inference(unflattening,[status(thm)],[c_585]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_587,plain,
% 2.92/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_586]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_4712,plain,
% 2.92/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.92/1.00      inference(global_propositional_subsumption,[status(thm)],[c_4649,c_587]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_5312,plain,
% 2.92/1.00      ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top ),
% 2.92/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_5304,c_4712]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_5317,plain,
% 2.92/1.00      ( $false ),
% 2.92/1.00      inference(superposition,[status(thm)],[c_2102,c_5312]) ).
% 2.92/1.00  
% 2.92/1.00  
% 2.92/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.92/1.00  
% 2.92/1.00  ------                               Statistics
% 2.92/1.00  
% 2.92/1.00  ------ General
% 2.92/1.00  
% 2.92/1.00  abstr_ref_over_cycles:                  0
% 2.92/1.00  abstr_ref_under_cycles:                 0
% 2.92/1.00  gc_basic_clause_elim:                   0
% 2.92/1.00  forced_gc_time:                         0
% 2.92/1.00  parsing_time:                           0.01
% 2.92/1.00  unif_index_cands_time:                  0.
% 2.92/1.00  unif_index_add_time:                    0.
% 2.92/1.00  orderings_time:                         0.
% 2.92/1.00  out_proof_time:                         0.013
% 2.92/1.00  total_time:                             0.171
% 2.92/1.00  num_of_symbols:                         54
% 2.92/1.00  num_of_terms:                           6329
% 2.92/1.00  
% 2.92/1.00  ------ Preprocessing
% 2.92/1.00  
% 2.92/1.00  num_of_splits:                          0
% 2.92/1.00  num_of_split_atoms:                     0
% 2.92/1.00  num_of_reused_defs:                     0
% 2.92/1.00  num_eq_ax_congr_red:                    28
% 2.92/1.00  num_of_sem_filtered_clauses:            1
% 2.92/1.00  num_of_subtypes:                        0
% 2.92/1.00  monotx_restored_types:                  0
% 2.92/1.00  sat_num_of_epr_types:                   0
% 2.92/1.00  sat_num_of_non_cyclic_types:            0
% 2.92/1.00  sat_guarded_non_collapsed_types:        0
% 2.92/1.00  num_pure_diseq_elim:                    0
% 2.92/1.00  simp_replaced_by:                       0
% 2.92/1.00  res_preprocessed:                       174
% 2.92/1.00  prep_upred:                             0
% 2.92/1.00  prep_unflattend:                        94
% 2.92/1.00  smt_new_axioms:                         0
% 2.92/1.00  pred_elim_cands:                        4
% 2.92/1.00  pred_elim:                              3
% 2.92/1.00  pred_elim_cl:                           7
% 2.92/1.00  pred_elim_cycles:                       7
% 2.92/1.00  merged_defs:                            0
% 2.92/1.00  merged_defs_ncl:                        0
% 2.92/1.00  bin_hyper_res:                          0
% 2.92/1.00  prep_cycles:                            4
% 2.92/1.00  pred_elim_time:                         0.016
% 2.92/1.00  splitting_time:                         0.
% 2.92/1.00  sem_filter_time:                        0.
% 2.92/1.00  monotx_time:                            0.
% 2.92/1.00  subtype_inf_time:                       0.
% 2.92/1.00  
% 2.92/1.00  ------ Problem properties
% 2.92/1.00  
% 2.92/1.00  clauses:                                34
% 2.92/1.00  conjectures:                            3
% 2.92/1.00  epr:                                    3
% 2.92/1.00  horn:                                   29
% 2.92/1.00  ground:                                 6
% 2.92/1.00  unary:                                  16
% 2.92/1.00  binary:                                 4
% 2.92/1.00  lits:                                   75
% 2.92/1.00  lits_eq:                                35
% 2.92/1.00  fd_pure:                                0
% 2.92/1.00  fd_pseudo:                              0
% 2.92/1.00  fd_cond:                                2
% 2.92/1.00  fd_pseudo_cond:                         4
% 2.92/1.00  ac_symbols:                             0
% 2.92/1.00  
% 2.92/1.00  ------ Propositional Solver
% 2.92/1.00  
% 2.92/1.00  prop_solver_calls:                      27
% 2.92/1.00  prop_fast_solver_calls:                 1133
% 2.92/1.00  smt_solver_calls:                       0
% 2.92/1.00  smt_fast_solver_calls:                  0
% 2.92/1.00  prop_num_of_clauses:                    1671
% 2.92/1.00  prop_preprocess_simplified:             7434
% 2.92/1.00  prop_fo_subsumed:                       14
% 2.92/1.00  prop_solver_time:                       0.
% 2.92/1.00  smt_solver_time:                        0.
% 2.92/1.00  smt_fast_solver_time:                   0.
% 2.92/1.00  prop_fast_solver_time:                  0.
% 2.92/1.00  prop_unsat_core_time:                   0.
% 2.92/1.00  
% 2.92/1.00  ------ QBF
% 2.92/1.00  
% 2.92/1.00  qbf_q_res:                              0
% 2.92/1.00  qbf_num_tautologies:                    0
% 2.92/1.00  qbf_prep_cycles:                        0
% 2.92/1.00  
% 2.92/1.00  ------ BMC1
% 2.92/1.00  
% 2.92/1.00  bmc1_current_bound:                     -1
% 2.92/1.00  bmc1_last_solved_bound:                 -1
% 2.92/1.00  bmc1_unsat_core_size:                   -1
% 2.92/1.00  bmc1_unsat_core_parents_size:           -1
% 2.92/1.00  bmc1_merge_next_fun:                    0
% 2.92/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.92/1.00  
% 2.92/1.00  ------ Instantiation
% 2.92/1.00  
% 2.92/1.00  inst_num_of_clauses:                    532
% 2.92/1.00  inst_num_in_passive:                    216
% 2.92/1.00  inst_num_in_active:                     225
% 2.92/1.00  inst_num_in_unprocessed:                91
% 2.92/1.00  inst_num_of_loops:                      260
% 2.92/1.00  inst_num_of_learning_restarts:          0
% 2.92/1.00  inst_num_moves_active_passive:          33
% 2.92/1.00  inst_lit_activity:                      0
% 2.92/1.00  inst_lit_activity_moves:                0
% 2.92/1.00  inst_num_tautologies:                   0
% 2.92/1.00  inst_num_prop_implied:                  0
% 2.92/1.00  inst_num_existing_simplified:           0
% 2.92/1.00  inst_num_eq_res_simplified:             0
% 2.92/1.00  inst_num_child_elim:                    0
% 2.92/1.00  inst_num_of_dismatching_blockings:      228
% 2.92/1.00  inst_num_of_non_proper_insts:           390
% 2.92/1.00  inst_num_of_duplicates:                 0
% 2.92/1.00  inst_inst_num_from_inst_to_res:         0
% 2.92/1.00  inst_dismatching_checking_time:         0.
% 2.92/1.00  
% 2.92/1.00  ------ Resolution
% 2.92/1.00  
% 2.92/1.00  res_num_of_clauses:                     0
% 2.92/1.00  res_num_in_passive:                     0
% 2.92/1.00  res_num_in_active:                      0
% 2.92/1.00  res_num_of_loops:                       178
% 2.92/1.00  res_forward_subset_subsumed:            59
% 2.92/1.00  res_backward_subset_subsumed:           0
% 2.92/1.00  res_forward_subsumed:                   2
% 2.92/1.00  res_backward_subsumed:                  0
% 2.92/1.00  res_forward_subsumption_resolution:     0
% 2.92/1.00  res_backward_subsumption_resolution:    0
% 2.92/1.00  res_clause_to_clause_subsumption:       302
% 2.92/1.00  res_orphan_elimination:                 0
% 2.92/1.00  res_tautology_del:                      34
% 2.92/1.00  res_num_eq_res_simplified:              0
% 2.92/1.00  res_num_sel_changes:                    0
% 2.92/1.00  res_moves_from_active_to_pass:          0
% 2.92/1.00  
% 2.92/1.00  ------ Superposition
% 2.92/1.00  
% 2.92/1.00  sup_time_total:                         0.
% 2.92/1.00  sup_time_generating:                    0.
% 2.92/1.00  sup_time_sim_full:                      0.
% 2.92/1.00  sup_time_sim_immed:                     0.
% 2.92/1.00  
% 2.92/1.00  sup_num_of_clauses:                     47
% 2.92/1.00  sup_num_in_active:                      39
% 2.92/1.00  sup_num_in_passive:                     8
% 2.92/1.00  sup_num_of_loops:                       50
% 2.92/1.00  sup_fw_superposition:                   25
% 2.92/1.00  sup_bw_superposition:                   5
% 2.92/1.00  sup_immediate_simplified:               4
% 2.92/1.00  sup_given_eliminated:                   0
% 2.92/1.00  comparisons_done:                       0
% 2.92/1.00  comparisons_avoided:                    4
% 2.92/1.00  
% 2.92/1.00  ------ Simplifications
% 2.92/1.00  
% 2.92/1.00  
% 2.92/1.00  sim_fw_subset_subsumed:                 1
% 2.92/1.00  sim_bw_subset_subsumed:                 0
% 2.92/1.00  sim_fw_subsumed:                        4
% 2.92/1.00  sim_bw_subsumed:                        0
% 2.92/1.00  sim_fw_subsumption_res:                 1
% 2.92/1.00  sim_bw_subsumption_res:                 0
% 2.92/1.00  sim_tautology_del:                      0
% 2.92/1.00  sim_eq_tautology_del:                   9
% 2.92/1.00  sim_eq_res_simp:                        0
% 2.92/1.00  sim_fw_demodulated:                     0
% 2.92/1.00  sim_bw_demodulated:                     12
% 2.92/1.00  sim_light_normalised:                   0
% 2.92/1.00  sim_joinable_taut:                      0
% 2.92/1.00  sim_joinable_simp:                      0
% 2.92/1.00  sim_ac_normalised:                      0
% 2.92/1.00  sim_smt_subsumption:                    0
% 2.92/1.00  
%------------------------------------------------------------------------------
