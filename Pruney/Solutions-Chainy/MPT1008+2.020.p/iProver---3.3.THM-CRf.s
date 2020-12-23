%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:08 EST 2020

% Result     : Theorem 1.07s
% Output     : CNFRefutation 1.07s
% Verified   : 
% Statistics : Number of formulae       :  173 (1067 expanded)
%              Number of clauses        :   82 ( 225 expanded)
%              Number of leaves         :   23 ( 269 expanded)
%              Depth                    :   19
%              Number of atoms          :  492 (2954 expanded)
%              Number of equality atoms :  262 (1537 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f34,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f35,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f49,plain,
    ( ? [X0,X1,X2] :
        ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( k1_tarski(k1_funct_1(sK4,sK2)) != k2_relset_1(k1_tarski(sK2),sK3,sK4)
      & k1_xboole_0 != sK3
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))
      & v1_funct_2(sK4,k1_tarski(sK2),sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( k1_tarski(k1_funct_1(sK4,sK2)) != k2_relset_1(k1_tarski(sK2),sK3,sK4)
    & k1_xboole_0 != sK3
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))
    & v1_funct_2(sK4,k1_tarski(sK2),sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f35,f49])).

fof(f87,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) ),
    inference(cnf_transformation,[],[f50])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f90,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f62,f63])).

fof(f91,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f61,f90])).

fof(f105,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) ),
    inference(definition_unfolding,[],[f87,f91])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
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
    inference(nnf_transformation,[],[f3])).

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

fof(f95,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f57,f90])).

fof(f109,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f95])).

fof(f110,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_enumset1(X0,X0,X0,X4)) ),
    inference(equality_resolution,[],[f109])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f32])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f86,plain,(
    v1_funct_2(sK4,k1_tarski(sK2),sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f106,plain,(
    v1_funct_2(sK4,k2_enumset1(sK2,sK2,sK2,sK2),sK3) ),
    inference(definition_unfolding,[],[f86,f91])).

fof(f85,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f50])).

fof(f88,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f50])).

fof(f17,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_tarski(X2) = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_tarski(X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_tarski(X2) = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_tarski(X2) = k1_funct_1(sK1(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK1(X0)) = X0
        & v1_funct_1(sK1(X0))
        & v1_relat_1(sK1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_tarski(X2) = k1_funct_1(sK1(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK1(X0)) = X0
      & v1_funct_1(sK1(X0))
      & v1_relat_1(sK1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f47])).

fof(f83,plain,(
    ! [X2,X0] :
      ( k1_tarski(X2) = k1_funct_1(sK1(X0),X2)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f103,plain,(
    ! [X2,X0] :
      ( k2_enumset1(X2,X2,X2,X2) = k1_funct_1(sK1(X0),X2)
      | ~ r2_hidden(X2,X0) ) ),
    inference(definition_unfolding,[],[f83,f91])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f101,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_enumset1(X0,X0,X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f67,f91])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f82,plain,(
    ! [X0] : k1_relat_1(sK1(X0)) = X0 ),
    inference(cnf_transformation,[],[f48])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f74,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f80,plain,(
    ! [X0] : v1_relat_1(sK1(X0)) ),
    inference(cnf_transformation,[],[f48])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f43])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f100,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f64,f91,f91])).

fof(f89,plain,(
    k1_tarski(k1_funct_1(sK4,sK2)) != k2_relset_1(k1_tarski(sK2),sK3,sK4) ),
    inference(cnf_transformation,[],[f50])).

fof(f104,plain,(
    k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) != k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) ),
    inference(definition_unfolding,[],[f89,f91,f91])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f102,plain,(
    ! [X0,X1] :
      ( k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f76,f91,f91])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f53,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f96,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f56,f90])).

fof(f111,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f96])).

fof(f112,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_enumset1(X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f111])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1915,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1919,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4288,plain,
    ( k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1915,c_1919])).

cnf(c_7,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1932,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK4,k2_enumset1(sK2,sK2,sK2,sK2),sK3) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_414,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | k2_enumset1(sK2,sK2,sK2,sK2) != X1
    | sK3 != X2
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_34])).

cnf(c_415,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)))
    | ~ r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2))
    | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4))
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_414])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_32,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_419,plain,
    ( ~ r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2))
    | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_415,c_35,c_33,c_32])).

cnf(c_1913,plain,
    ( r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_419])).

cnf(c_26,plain,
    ( ~ r2_hidden(X0,X1)
    | k2_enumset1(X0,X0,X0,X0) = k1_funct_1(sK1(X1),X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1918,plain,
    ( k2_enumset1(X0,X0,X0,X0) = k1_funct_1(sK1(X1),X0)
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3063,plain,
    ( k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k1_funct_1(sK1(k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4)),k1_funct_1(sK4,X0))
    | r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1913,c_1918])).

cnf(c_3254,plain,
    ( k1_funct_1(sK1(k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4)),k1_funct_1(sK4,sK2)) = k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) ),
    inference(superposition,[status(thm)],[c_1932,c_3063])).

cnf(c_4475,plain,
    ( k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) = k1_funct_1(sK1(k2_relat_1(sK4)),k1_funct_1(sK4,sK2)) ),
    inference(demodulation,[status(thm)],[c_4288,c_3254])).

cnf(c_13,plain,
    ( m1_subset_1(k2_enumset1(X0,X0,X0,X0),k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1926,plain,
    ( m1_subset_1(k2_enumset1(X0,X0,X0,X0),k1_zfmisc_1(X1)) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4811,plain,
    ( m1_subset_1(k1_funct_1(sK1(k2_relat_1(sK4)),k1_funct_1(sK4,sK2)),k1_zfmisc_1(X0)) = iProver_top
    | r2_hidden(k1_funct_1(sK4,sK2),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4475,c_1926])).

cnf(c_18,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_27,plain,
    ( k1_relat_1(sK1(X0)) = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_21,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1922,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3191,plain,
    ( sK1(X0) = k1_xboole_0
    | k1_xboole_0 != X0
    | v1_relat_1(sK1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_27,c_1922])).

cnf(c_29,plain,
    ( v1_relat_1(sK1(X0)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_42,plain,
    ( v1_relat_1(sK1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3245,plain,
    ( k1_xboole_0 != X0
    | sK1(X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3191,c_42])).

cnf(c_3246,plain,
    ( sK1(X0) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(renaming,[status(thm)],[c_3245])).

cnf(c_3250,plain,
    ( sK1(k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_3246])).

cnf(c_24,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_17,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_469,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_24,c_17])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_473,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_469,c_23])).

cnf(c_474,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_473])).

cnf(c_1912,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_474])).

cnf(c_2264,plain,
    ( r1_tarski(k1_relat_1(sK4),k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1915,c_1912])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1927,plain,
    ( k2_enumset1(X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4427,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_relat_1(sK4)
    | k1_relat_1(sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2264,c_1927])).

cnf(c_38,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_31,negated_conjecture,
    ( k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) != k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_22,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_449,plain,
    ( ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_35])).

cnf(c_450,plain,
    ( ~ v1_relat_1(sK4)
    | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK4)
    | k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k2_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_449])).

cnf(c_451,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK4)
    | k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k2_relat_1(sK4)
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_450])).

cnf(c_453,plain,
    ( k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) = k2_relat_1(sK4)
    | k2_enumset1(sK2,sK2,sK2,sK2) != k1_relat_1(sK4)
    | v1_relat_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_451])).

cnf(c_2119,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_2120,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2119])).

cnf(c_2170,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)))
    | k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) = k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_1271,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2152,plain,
    ( k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) != X0
    | k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) = k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4)
    | k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) != X0 ),
    inference(instantiation,[status(thm)],[c_1271])).

cnf(c_2380,plain,
    ( k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) = k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4)
    | k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) != k2_relat_1(sK4)
    | k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) != k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2152])).

cnf(c_5319,plain,
    ( k1_relat_1(sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4427,c_33,c_38,c_31,c_453,c_2120,c_2170,c_2380])).

cnf(c_5328,plain,
    ( sK4 = k1_xboole_0
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5319,c_1922])).

cnf(c_5375,plain,
    ( sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5328,c_38,c_2120])).

cnf(c_6298,plain,
    ( m1_subset_1(k1_funct_1(k1_xboole_0,k1_funct_1(k1_xboole_0,sK2)),k1_zfmisc_1(X0)) = iProver_top
    | r2_hidden(k1_funct_1(k1_xboole_0,sK2),X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4811,c_18,c_3250,c_5375])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1924,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_6304,plain,
    ( r2_hidden(k1_funct_1(k1_xboole_0,sK2),X0) != iProver_top
    | r1_tarski(k1_funct_1(k1_xboole_0,k1_funct_1(k1_xboole_0,sK2)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6298,c_1924])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1936,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1938,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4310,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1936,c_1938])).

cnf(c_7623,plain,
    ( k1_funct_1(k1_xboole_0,k1_funct_1(k1_xboole_0,sK2)) = k1_xboole_0
    | r2_hidden(k1_funct_1(k1_xboole_0,sK2),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6304,c_4310])).

cnf(c_4477,plain,
    ( r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4288,c_1913])).

cnf(c_5384,plain,
    ( r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
    | r2_hidden(k1_funct_1(k1_xboole_0,X0),k2_relat_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5375,c_4477])).

cnf(c_5406,plain,
    ( r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
    | r2_hidden(k1_funct_1(k1_xboole_0,X0),k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5384,c_18])).

cnf(c_5431,plain,
    ( r2_hidden(k1_funct_1(k1_xboole_0,sK2),k1_xboole_0) = iProver_top
    | r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5406])).

cnf(c_3376,plain,
    ( k1_funct_1(sK1(k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4)),k1_funct_1(sK4,sK2)) != k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_3254,c_31])).

cnf(c_4474,plain,
    ( k1_funct_1(sK1(k2_relat_1(sK4)),k1_funct_1(sK4,sK2)) != k2_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_4288,c_3376])).

cnf(c_5386,plain,
    ( k1_funct_1(sK1(k2_relat_1(k1_xboole_0)),k1_funct_1(k1_xboole_0,sK2)) != k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_5375,c_4474])).

cnf(c_5399,plain,
    ( k1_funct_1(k1_xboole_0,k1_funct_1(k1_xboole_0,sK2)) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5386,c_18,c_3250])).

cnf(c_8,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_97,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_99,plain,
    ( r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_97])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7623,c_5431,c_5399,c_99])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:34:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.07/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.07/1.03  
% 1.07/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.07/1.03  
% 1.07/1.03  ------  iProver source info
% 1.07/1.03  
% 1.07/1.03  git: date: 2020-06-30 10:37:57 +0100
% 1.07/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.07/1.03  git: non_committed_changes: false
% 1.07/1.03  git: last_make_outside_of_git: false
% 1.07/1.03  
% 1.07/1.03  ------ 
% 1.07/1.03  
% 1.07/1.03  ------ Input Options
% 1.07/1.03  
% 1.07/1.03  --out_options                           all
% 1.07/1.03  --tptp_safe_out                         true
% 1.07/1.03  --problem_path                          ""
% 1.07/1.03  --include_path                          ""
% 1.07/1.03  --clausifier                            res/vclausify_rel
% 1.07/1.03  --clausifier_options                    --mode clausify
% 1.07/1.03  --stdin                                 false
% 1.07/1.03  --stats_out                             all
% 1.07/1.03  
% 1.07/1.03  ------ General Options
% 1.07/1.03  
% 1.07/1.03  --fof                                   false
% 1.07/1.03  --time_out_real                         305.
% 1.07/1.03  --time_out_virtual                      -1.
% 1.07/1.03  --symbol_type_check                     false
% 1.07/1.03  --clausify_out                          false
% 1.07/1.03  --sig_cnt_out                           false
% 1.07/1.03  --trig_cnt_out                          false
% 1.07/1.03  --trig_cnt_out_tolerance                1.
% 1.07/1.03  --trig_cnt_out_sk_spl                   false
% 1.07/1.03  --abstr_cl_out                          false
% 1.07/1.03  
% 1.07/1.03  ------ Global Options
% 1.07/1.03  
% 1.07/1.03  --schedule                              default
% 1.07/1.03  --add_important_lit                     false
% 1.07/1.03  --prop_solver_per_cl                    1000
% 1.07/1.03  --min_unsat_core                        false
% 1.07/1.03  --soft_assumptions                      false
% 1.07/1.03  --soft_lemma_size                       3
% 1.07/1.03  --prop_impl_unit_size                   0
% 1.07/1.03  --prop_impl_unit                        []
% 1.07/1.03  --share_sel_clauses                     true
% 1.07/1.03  --reset_solvers                         false
% 1.07/1.03  --bc_imp_inh                            [conj_cone]
% 1.07/1.03  --conj_cone_tolerance                   3.
% 1.07/1.03  --extra_neg_conj                        none
% 1.07/1.03  --large_theory_mode                     true
% 1.07/1.03  --prolific_symb_bound                   200
% 1.07/1.03  --lt_threshold                          2000
% 1.07/1.03  --clause_weak_htbl                      true
% 1.07/1.03  --gc_record_bc_elim                     false
% 1.07/1.03  
% 1.07/1.03  ------ Preprocessing Options
% 1.07/1.03  
% 1.07/1.03  --preprocessing_flag                    true
% 1.07/1.03  --time_out_prep_mult                    0.1
% 1.07/1.03  --splitting_mode                        input
% 1.07/1.03  --splitting_grd                         true
% 1.07/1.03  --splitting_cvd                         false
% 1.07/1.03  --splitting_cvd_svl                     false
% 1.07/1.03  --splitting_nvd                         32
% 1.07/1.03  --sub_typing                            true
% 1.07/1.03  --prep_gs_sim                           true
% 1.07/1.03  --prep_unflatten                        true
% 1.07/1.03  --prep_res_sim                          true
% 1.07/1.03  --prep_upred                            true
% 1.07/1.03  --prep_sem_filter                       exhaustive
% 1.07/1.03  --prep_sem_filter_out                   false
% 1.07/1.03  --pred_elim                             true
% 1.07/1.03  --res_sim_input                         true
% 1.07/1.03  --eq_ax_congr_red                       true
% 1.07/1.03  --pure_diseq_elim                       true
% 1.07/1.03  --brand_transform                       false
% 1.07/1.03  --non_eq_to_eq                          false
% 1.07/1.03  --prep_def_merge                        true
% 1.07/1.03  --prep_def_merge_prop_impl              false
% 1.07/1.03  --prep_def_merge_mbd                    true
% 1.07/1.03  --prep_def_merge_tr_red                 false
% 1.07/1.03  --prep_def_merge_tr_cl                  false
% 1.07/1.03  --smt_preprocessing                     true
% 1.07/1.03  --smt_ac_axioms                         fast
% 1.07/1.03  --preprocessed_out                      false
% 1.07/1.03  --preprocessed_stats                    false
% 1.07/1.03  
% 1.07/1.03  ------ Abstraction refinement Options
% 1.07/1.03  
% 1.07/1.03  --abstr_ref                             []
% 1.07/1.03  --abstr_ref_prep                        false
% 1.07/1.03  --abstr_ref_until_sat                   false
% 1.07/1.03  --abstr_ref_sig_restrict                funpre
% 1.07/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 1.07/1.03  --abstr_ref_under                       []
% 1.07/1.03  
% 1.07/1.03  ------ SAT Options
% 1.07/1.03  
% 1.07/1.03  --sat_mode                              false
% 1.07/1.03  --sat_fm_restart_options                ""
% 1.07/1.03  --sat_gr_def                            false
% 1.07/1.03  --sat_epr_types                         true
% 1.07/1.03  --sat_non_cyclic_types                  false
% 1.07/1.03  --sat_finite_models                     false
% 1.07/1.03  --sat_fm_lemmas                         false
% 1.07/1.03  --sat_fm_prep                           false
% 1.07/1.03  --sat_fm_uc_incr                        true
% 1.07/1.03  --sat_out_model                         small
% 1.07/1.03  --sat_out_clauses                       false
% 1.07/1.03  
% 1.07/1.03  ------ QBF Options
% 1.07/1.03  
% 1.07/1.03  --qbf_mode                              false
% 1.07/1.03  --qbf_elim_univ                         false
% 1.07/1.03  --qbf_dom_inst                          none
% 1.07/1.03  --qbf_dom_pre_inst                      false
% 1.07/1.03  --qbf_sk_in                             false
% 1.07/1.03  --qbf_pred_elim                         true
% 1.07/1.03  --qbf_split                             512
% 1.07/1.03  
% 1.07/1.03  ------ BMC1 Options
% 1.07/1.03  
% 1.07/1.03  --bmc1_incremental                      false
% 1.07/1.03  --bmc1_axioms                           reachable_all
% 1.07/1.03  --bmc1_min_bound                        0
% 1.07/1.03  --bmc1_max_bound                        -1
% 1.07/1.03  --bmc1_max_bound_default                -1
% 1.07/1.03  --bmc1_symbol_reachability              true
% 1.07/1.03  --bmc1_property_lemmas                  false
% 1.07/1.03  --bmc1_k_induction                      false
% 1.07/1.03  --bmc1_non_equiv_states                 false
% 1.07/1.03  --bmc1_deadlock                         false
% 1.07/1.03  --bmc1_ucm                              false
% 1.07/1.03  --bmc1_add_unsat_core                   none
% 1.07/1.03  --bmc1_unsat_core_children              false
% 1.07/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 1.07/1.03  --bmc1_out_stat                         full
% 1.07/1.03  --bmc1_ground_init                      false
% 1.07/1.03  --bmc1_pre_inst_next_state              false
% 1.07/1.03  --bmc1_pre_inst_state                   false
% 1.07/1.03  --bmc1_pre_inst_reach_state             false
% 1.07/1.03  --bmc1_out_unsat_core                   false
% 1.07/1.03  --bmc1_aig_witness_out                  false
% 1.07/1.03  --bmc1_verbose                          false
% 1.07/1.03  --bmc1_dump_clauses_tptp                false
% 1.07/1.03  --bmc1_dump_unsat_core_tptp             false
% 1.07/1.03  --bmc1_dump_file                        -
% 1.07/1.03  --bmc1_ucm_expand_uc_limit              128
% 1.07/1.03  --bmc1_ucm_n_expand_iterations          6
% 1.07/1.03  --bmc1_ucm_extend_mode                  1
% 1.07/1.03  --bmc1_ucm_init_mode                    2
% 1.07/1.03  --bmc1_ucm_cone_mode                    none
% 1.07/1.03  --bmc1_ucm_reduced_relation_type        0
% 1.07/1.03  --bmc1_ucm_relax_model                  4
% 1.07/1.03  --bmc1_ucm_full_tr_after_sat            true
% 1.07/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 1.07/1.03  --bmc1_ucm_layered_model                none
% 1.07/1.03  --bmc1_ucm_max_lemma_size               10
% 1.07/1.03  
% 1.07/1.03  ------ AIG Options
% 1.07/1.03  
% 1.07/1.03  --aig_mode                              false
% 1.07/1.03  
% 1.07/1.03  ------ Instantiation Options
% 1.07/1.03  
% 1.07/1.03  --instantiation_flag                    true
% 1.07/1.03  --inst_sos_flag                         false
% 1.07/1.03  --inst_sos_phase                        true
% 1.07/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.07/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.07/1.03  --inst_lit_sel_side                     num_symb
% 1.07/1.03  --inst_solver_per_active                1400
% 1.07/1.03  --inst_solver_calls_frac                1.
% 1.07/1.03  --inst_passive_queue_type               priority_queues
% 1.07/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.07/1.03  --inst_passive_queues_freq              [25;2]
% 1.07/1.03  --inst_dismatching                      true
% 1.07/1.03  --inst_eager_unprocessed_to_passive     true
% 1.07/1.03  --inst_prop_sim_given                   true
% 1.07/1.03  --inst_prop_sim_new                     false
% 1.07/1.03  --inst_subs_new                         false
% 1.07/1.03  --inst_eq_res_simp                      false
% 1.07/1.03  --inst_subs_given                       false
% 1.07/1.03  --inst_orphan_elimination               true
% 1.07/1.03  --inst_learning_loop_flag               true
% 1.07/1.03  --inst_learning_start                   3000
% 1.07/1.03  --inst_learning_factor                  2
% 1.07/1.03  --inst_start_prop_sim_after_learn       3
% 1.07/1.03  --inst_sel_renew                        solver
% 1.07/1.03  --inst_lit_activity_flag                true
% 1.07/1.03  --inst_restr_to_given                   false
% 1.07/1.03  --inst_activity_threshold               500
% 1.07/1.03  --inst_out_proof                        true
% 1.07/1.03  
% 1.07/1.03  ------ Resolution Options
% 1.07/1.03  
% 1.07/1.03  --resolution_flag                       true
% 1.07/1.03  --res_lit_sel                           adaptive
% 1.07/1.03  --res_lit_sel_side                      none
% 1.07/1.03  --res_ordering                          kbo
% 1.07/1.03  --res_to_prop_solver                    active
% 1.07/1.03  --res_prop_simpl_new                    false
% 1.07/1.03  --res_prop_simpl_given                  true
% 1.07/1.03  --res_passive_queue_type                priority_queues
% 1.07/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.07/1.03  --res_passive_queues_freq               [15;5]
% 1.07/1.03  --res_forward_subs                      full
% 1.07/1.03  --res_backward_subs                     full
% 1.07/1.03  --res_forward_subs_resolution           true
% 1.07/1.03  --res_backward_subs_resolution          true
% 1.07/1.03  --res_orphan_elimination                true
% 1.07/1.03  --res_time_limit                        2.
% 1.07/1.03  --res_out_proof                         true
% 1.07/1.03  
% 1.07/1.03  ------ Superposition Options
% 1.07/1.03  
% 1.07/1.03  --superposition_flag                    true
% 1.07/1.03  --sup_passive_queue_type                priority_queues
% 1.07/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.07/1.03  --sup_passive_queues_freq               [8;1;4]
% 1.07/1.03  --demod_completeness_check              fast
% 1.07/1.03  --demod_use_ground                      true
% 1.07/1.03  --sup_to_prop_solver                    passive
% 1.07/1.03  --sup_prop_simpl_new                    true
% 1.07/1.03  --sup_prop_simpl_given                  true
% 1.07/1.03  --sup_fun_splitting                     false
% 1.07/1.03  --sup_smt_interval                      50000
% 1.07/1.03  
% 1.07/1.03  ------ Superposition Simplification Setup
% 1.07/1.03  
% 1.07/1.03  --sup_indices_passive                   []
% 1.07/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.07/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.07/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.07/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 1.07/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.07/1.03  --sup_full_bw                           [BwDemod]
% 1.07/1.03  --sup_immed_triv                        [TrivRules]
% 1.07/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.07/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.07/1.03  --sup_immed_bw_main                     []
% 1.07/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.07/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 1.07/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.07/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.07/1.03  
% 1.07/1.03  ------ Combination Options
% 1.07/1.03  
% 1.07/1.03  --comb_res_mult                         3
% 1.07/1.03  --comb_sup_mult                         2
% 1.07/1.03  --comb_inst_mult                        10
% 1.07/1.03  
% 1.07/1.03  ------ Debug Options
% 1.07/1.03  
% 1.07/1.03  --dbg_backtrace                         false
% 1.07/1.03  --dbg_dump_prop_clauses                 false
% 1.07/1.03  --dbg_dump_prop_clauses_file            -
% 1.07/1.03  --dbg_out_stat                          false
% 1.07/1.03  ------ Parsing...
% 1.07/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.07/1.03  
% 1.07/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 1.07/1.03  
% 1.07/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.07/1.03  
% 1.07/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.07/1.03  ------ Proving...
% 1.07/1.03  ------ Problem Properties 
% 1.07/1.03  
% 1.07/1.03  
% 1.07/1.03  clauses                                 32
% 1.07/1.03  conjectures                             4
% 1.07/1.03  EPR                                     5
% 1.07/1.03  Horn                                    29
% 1.07/1.03  unary                                   15
% 1.07/1.03  binary                                  8
% 1.07/1.03  lits                                    60
% 1.07/1.03  lits eq                                 25
% 1.07/1.03  fd_pure                                 0
% 1.07/1.03  fd_pseudo                               0
% 1.07/1.03  fd_cond                                 2
% 1.07/1.03  fd_pseudo_cond                          5
% 1.07/1.03  AC symbols                              0
% 1.07/1.03  
% 1.07/1.03  ------ Schedule dynamic 5 is on 
% 1.07/1.03  
% 1.07/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.07/1.03  
% 1.07/1.03  
% 1.07/1.03  ------ 
% 1.07/1.03  Current options:
% 1.07/1.03  ------ 
% 1.07/1.03  
% 1.07/1.03  ------ Input Options
% 1.07/1.03  
% 1.07/1.03  --out_options                           all
% 1.07/1.03  --tptp_safe_out                         true
% 1.07/1.03  --problem_path                          ""
% 1.07/1.03  --include_path                          ""
% 1.07/1.03  --clausifier                            res/vclausify_rel
% 1.07/1.03  --clausifier_options                    --mode clausify
% 1.07/1.03  --stdin                                 false
% 1.07/1.03  --stats_out                             all
% 1.07/1.03  
% 1.07/1.03  ------ General Options
% 1.07/1.03  
% 1.07/1.03  --fof                                   false
% 1.07/1.03  --time_out_real                         305.
% 1.07/1.03  --time_out_virtual                      -1.
% 1.07/1.03  --symbol_type_check                     false
% 1.07/1.03  --clausify_out                          false
% 1.07/1.03  --sig_cnt_out                           false
% 1.07/1.03  --trig_cnt_out                          false
% 1.07/1.03  --trig_cnt_out_tolerance                1.
% 1.07/1.03  --trig_cnt_out_sk_spl                   false
% 1.07/1.03  --abstr_cl_out                          false
% 1.07/1.03  
% 1.07/1.03  ------ Global Options
% 1.07/1.03  
% 1.07/1.03  --schedule                              default
% 1.07/1.03  --add_important_lit                     false
% 1.07/1.03  --prop_solver_per_cl                    1000
% 1.07/1.03  --min_unsat_core                        false
% 1.07/1.03  --soft_assumptions                      false
% 1.07/1.03  --soft_lemma_size                       3
% 1.07/1.03  --prop_impl_unit_size                   0
% 1.07/1.03  --prop_impl_unit                        []
% 1.07/1.03  --share_sel_clauses                     true
% 1.07/1.03  --reset_solvers                         false
% 1.07/1.03  --bc_imp_inh                            [conj_cone]
% 1.07/1.03  --conj_cone_tolerance                   3.
% 1.07/1.03  --extra_neg_conj                        none
% 1.07/1.03  --large_theory_mode                     true
% 1.07/1.03  --prolific_symb_bound                   200
% 1.07/1.03  --lt_threshold                          2000
% 1.07/1.03  --clause_weak_htbl                      true
% 1.07/1.03  --gc_record_bc_elim                     false
% 1.07/1.03  
% 1.07/1.03  ------ Preprocessing Options
% 1.07/1.03  
% 1.07/1.03  --preprocessing_flag                    true
% 1.07/1.03  --time_out_prep_mult                    0.1
% 1.07/1.03  --splitting_mode                        input
% 1.07/1.03  --splitting_grd                         true
% 1.07/1.03  --splitting_cvd                         false
% 1.07/1.03  --splitting_cvd_svl                     false
% 1.07/1.03  --splitting_nvd                         32
% 1.07/1.03  --sub_typing                            true
% 1.07/1.03  --prep_gs_sim                           true
% 1.07/1.03  --prep_unflatten                        true
% 1.07/1.03  --prep_res_sim                          true
% 1.07/1.03  --prep_upred                            true
% 1.07/1.03  --prep_sem_filter                       exhaustive
% 1.07/1.03  --prep_sem_filter_out                   false
% 1.07/1.03  --pred_elim                             true
% 1.07/1.03  --res_sim_input                         true
% 1.07/1.03  --eq_ax_congr_red                       true
% 1.07/1.03  --pure_diseq_elim                       true
% 1.07/1.03  --brand_transform                       false
% 1.07/1.03  --non_eq_to_eq                          false
% 1.07/1.03  --prep_def_merge                        true
% 1.07/1.03  --prep_def_merge_prop_impl              false
% 1.07/1.03  --prep_def_merge_mbd                    true
% 1.07/1.03  --prep_def_merge_tr_red                 false
% 1.07/1.03  --prep_def_merge_tr_cl                  false
% 1.07/1.03  --smt_preprocessing                     true
% 1.07/1.03  --smt_ac_axioms                         fast
% 1.07/1.03  --preprocessed_out                      false
% 1.07/1.03  --preprocessed_stats                    false
% 1.07/1.03  
% 1.07/1.03  ------ Abstraction refinement Options
% 1.07/1.03  
% 1.07/1.03  --abstr_ref                             []
% 1.07/1.03  --abstr_ref_prep                        false
% 1.07/1.03  --abstr_ref_until_sat                   false
% 1.07/1.03  --abstr_ref_sig_restrict                funpre
% 1.07/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 1.07/1.03  --abstr_ref_under                       []
% 1.07/1.03  
% 1.07/1.03  ------ SAT Options
% 1.07/1.03  
% 1.07/1.03  --sat_mode                              false
% 1.07/1.03  --sat_fm_restart_options                ""
% 1.07/1.03  --sat_gr_def                            false
% 1.07/1.03  --sat_epr_types                         true
% 1.07/1.03  --sat_non_cyclic_types                  false
% 1.07/1.03  --sat_finite_models                     false
% 1.07/1.03  --sat_fm_lemmas                         false
% 1.07/1.03  --sat_fm_prep                           false
% 1.07/1.03  --sat_fm_uc_incr                        true
% 1.07/1.03  --sat_out_model                         small
% 1.07/1.03  --sat_out_clauses                       false
% 1.07/1.03  
% 1.07/1.03  ------ QBF Options
% 1.07/1.03  
% 1.07/1.03  --qbf_mode                              false
% 1.07/1.03  --qbf_elim_univ                         false
% 1.07/1.03  --qbf_dom_inst                          none
% 1.07/1.03  --qbf_dom_pre_inst                      false
% 1.07/1.03  --qbf_sk_in                             false
% 1.07/1.03  --qbf_pred_elim                         true
% 1.07/1.03  --qbf_split                             512
% 1.07/1.03  
% 1.07/1.03  ------ BMC1 Options
% 1.07/1.03  
% 1.07/1.03  --bmc1_incremental                      false
% 1.07/1.03  --bmc1_axioms                           reachable_all
% 1.07/1.03  --bmc1_min_bound                        0
% 1.07/1.03  --bmc1_max_bound                        -1
% 1.07/1.03  --bmc1_max_bound_default                -1
% 1.07/1.03  --bmc1_symbol_reachability              true
% 1.07/1.03  --bmc1_property_lemmas                  false
% 1.07/1.03  --bmc1_k_induction                      false
% 1.07/1.03  --bmc1_non_equiv_states                 false
% 1.07/1.03  --bmc1_deadlock                         false
% 1.07/1.03  --bmc1_ucm                              false
% 1.07/1.03  --bmc1_add_unsat_core                   none
% 1.07/1.03  --bmc1_unsat_core_children              false
% 1.07/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 1.07/1.03  --bmc1_out_stat                         full
% 1.07/1.03  --bmc1_ground_init                      false
% 1.07/1.03  --bmc1_pre_inst_next_state              false
% 1.07/1.03  --bmc1_pre_inst_state                   false
% 1.07/1.03  --bmc1_pre_inst_reach_state             false
% 1.07/1.03  --bmc1_out_unsat_core                   false
% 1.07/1.03  --bmc1_aig_witness_out                  false
% 1.07/1.03  --bmc1_verbose                          false
% 1.07/1.03  --bmc1_dump_clauses_tptp                false
% 1.07/1.03  --bmc1_dump_unsat_core_tptp             false
% 1.07/1.03  --bmc1_dump_file                        -
% 1.07/1.03  --bmc1_ucm_expand_uc_limit              128
% 1.07/1.03  --bmc1_ucm_n_expand_iterations          6
% 1.07/1.03  --bmc1_ucm_extend_mode                  1
% 1.07/1.03  --bmc1_ucm_init_mode                    2
% 1.07/1.03  --bmc1_ucm_cone_mode                    none
% 1.07/1.03  --bmc1_ucm_reduced_relation_type        0
% 1.07/1.03  --bmc1_ucm_relax_model                  4
% 1.07/1.03  --bmc1_ucm_full_tr_after_sat            true
% 1.07/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 1.07/1.03  --bmc1_ucm_layered_model                none
% 1.07/1.03  --bmc1_ucm_max_lemma_size               10
% 1.07/1.03  
% 1.07/1.03  ------ AIG Options
% 1.07/1.03  
% 1.07/1.03  --aig_mode                              false
% 1.07/1.03  
% 1.07/1.03  ------ Instantiation Options
% 1.07/1.03  
% 1.07/1.03  --instantiation_flag                    true
% 1.07/1.03  --inst_sos_flag                         false
% 1.07/1.03  --inst_sos_phase                        true
% 1.07/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.07/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.07/1.03  --inst_lit_sel_side                     none
% 1.07/1.03  --inst_solver_per_active                1400
% 1.07/1.03  --inst_solver_calls_frac                1.
% 1.07/1.03  --inst_passive_queue_type               priority_queues
% 1.07/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.07/1.03  --inst_passive_queues_freq              [25;2]
% 1.07/1.03  --inst_dismatching                      true
% 1.07/1.03  --inst_eager_unprocessed_to_passive     true
% 1.07/1.03  --inst_prop_sim_given                   true
% 1.07/1.03  --inst_prop_sim_new                     false
% 1.07/1.03  --inst_subs_new                         false
% 1.07/1.03  --inst_eq_res_simp                      false
% 1.07/1.03  --inst_subs_given                       false
% 1.07/1.03  --inst_orphan_elimination               true
% 1.07/1.03  --inst_learning_loop_flag               true
% 1.07/1.03  --inst_learning_start                   3000
% 1.07/1.03  --inst_learning_factor                  2
% 1.07/1.03  --inst_start_prop_sim_after_learn       3
% 1.07/1.03  --inst_sel_renew                        solver
% 1.07/1.03  --inst_lit_activity_flag                true
% 1.07/1.03  --inst_restr_to_given                   false
% 1.07/1.03  --inst_activity_threshold               500
% 1.07/1.03  --inst_out_proof                        true
% 1.07/1.03  
% 1.07/1.03  ------ Resolution Options
% 1.07/1.03  
% 1.07/1.03  --resolution_flag                       false
% 1.07/1.03  --res_lit_sel                           adaptive
% 1.07/1.03  --res_lit_sel_side                      none
% 1.07/1.03  --res_ordering                          kbo
% 1.07/1.03  --res_to_prop_solver                    active
% 1.07/1.03  --res_prop_simpl_new                    false
% 1.07/1.03  --res_prop_simpl_given                  true
% 1.07/1.03  --res_passive_queue_type                priority_queues
% 1.07/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.07/1.03  --res_passive_queues_freq               [15;5]
% 1.07/1.03  --res_forward_subs                      full
% 1.07/1.03  --res_backward_subs                     full
% 1.07/1.03  --res_forward_subs_resolution           true
% 1.07/1.03  --res_backward_subs_resolution          true
% 1.07/1.03  --res_orphan_elimination                true
% 1.07/1.03  --res_time_limit                        2.
% 1.07/1.03  --res_out_proof                         true
% 1.07/1.03  
% 1.07/1.03  ------ Superposition Options
% 1.07/1.03  
% 1.07/1.03  --superposition_flag                    true
% 1.07/1.03  --sup_passive_queue_type                priority_queues
% 1.07/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.07/1.03  --sup_passive_queues_freq               [8;1;4]
% 1.07/1.03  --demod_completeness_check              fast
% 1.07/1.03  --demod_use_ground                      true
% 1.07/1.03  --sup_to_prop_solver                    passive
% 1.07/1.03  --sup_prop_simpl_new                    true
% 1.07/1.03  --sup_prop_simpl_given                  true
% 1.07/1.03  --sup_fun_splitting                     false
% 1.07/1.03  --sup_smt_interval                      50000
% 1.07/1.03  
% 1.07/1.03  ------ Superposition Simplification Setup
% 1.07/1.03  
% 1.07/1.03  --sup_indices_passive                   []
% 1.07/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.07/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.07/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.07/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 1.07/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.07/1.03  --sup_full_bw                           [BwDemod]
% 1.07/1.03  --sup_immed_triv                        [TrivRules]
% 1.07/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.07/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.07/1.03  --sup_immed_bw_main                     []
% 1.07/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.07/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 1.07/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.07/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.07/1.03  
% 1.07/1.03  ------ Combination Options
% 1.07/1.03  
% 1.07/1.03  --comb_res_mult                         3
% 1.07/1.03  --comb_sup_mult                         2
% 1.07/1.03  --comb_inst_mult                        10
% 1.07/1.03  
% 1.07/1.03  ------ Debug Options
% 1.07/1.03  
% 1.07/1.03  --dbg_backtrace                         false
% 1.07/1.03  --dbg_dump_prop_clauses                 false
% 1.07/1.03  --dbg_dump_prop_clauses_file            -
% 1.07/1.03  --dbg_out_stat                          false
% 1.07/1.03  
% 1.07/1.03  
% 1.07/1.03  
% 1.07/1.03  
% 1.07/1.03  ------ Proving...
% 1.07/1.03  
% 1.07/1.03  
% 1.07/1.03  % SZS status Theorem for theBenchmark.p
% 1.07/1.03  
% 1.07/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 1.07/1.03  
% 1.07/1.03  fof(f19,conjecture,(
% 1.07/1.03    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 1.07/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.07/1.03  
% 1.07/1.03  fof(f20,negated_conjecture,(
% 1.07/1.03    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 1.07/1.03    inference(negated_conjecture,[],[f19])).
% 1.07/1.03  
% 1.07/1.03  fof(f34,plain,(
% 1.07/1.03    ? [X0,X1,X2] : ((k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 1.07/1.03    inference(ennf_transformation,[],[f20])).
% 1.07/1.03  
% 1.07/1.03  fof(f35,plain,(
% 1.07/1.03    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 1.07/1.03    inference(flattening,[],[f34])).
% 1.07/1.03  
% 1.07/1.03  fof(f49,plain,(
% 1.07/1.03    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_tarski(k1_funct_1(sK4,sK2)) != k2_relset_1(k1_tarski(sK2),sK3,sK4) & k1_xboole_0 != sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) & v1_funct_2(sK4,k1_tarski(sK2),sK3) & v1_funct_1(sK4))),
% 1.07/1.03    introduced(choice_axiom,[])).
% 1.07/1.03  
% 1.07/1.03  fof(f50,plain,(
% 1.07/1.03    k1_tarski(k1_funct_1(sK4,sK2)) != k2_relset_1(k1_tarski(sK2),sK3,sK4) & k1_xboole_0 != sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) & v1_funct_2(sK4,k1_tarski(sK2),sK3) & v1_funct_1(sK4)),
% 1.07/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f35,f49])).
% 1.07/1.03  
% 1.07/1.03  fof(f87,plain,(
% 1.07/1.03    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))),
% 1.07/1.03    inference(cnf_transformation,[],[f50])).
% 1.07/1.03  
% 1.07/1.03  fof(f4,axiom,(
% 1.07/1.03    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.07/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.07/1.03  
% 1.07/1.03  fof(f61,plain,(
% 1.07/1.03    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.07/1.03    inference(cnf_transformation,[],[f4])).
% 1.07/1.03  
% 1.07/1.03  fof(f5,axiom,(
% 1.07/1.03    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.07/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.07/1.03  
% 1.07/1.03  fof(f62,plain,(
% 1.07/1.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.07/1.03    inference(cnf_transformation,[],[f5])).
% 1.07/1.03  
% 1.07/1.03  fof(f6,axiom,(
% 1.07/1.03    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.07/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.07/1.03  
% 1.07/1.03  fof(f63,plain,(
% 1.07/1.03    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.07/1.03    inference(cnf_transformation,[],[f6])).
% 1.07/1.03  
% 1.07/1.03  fof(f90,plain,(
% 1.07/1.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.07/1.03    inference(definition_unfolding,[],[f62,f63])).
% 1.07/1.03  
% 1.07/1.03  fof(f91,plain,(
% 1.07/1.03    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.07/1.03    inference(definition_unfolding,[],[f61,f90])).
% 1.07/1.03  
% 1.07/1.03  fof(f105,plain,(
% 1.07/1.03    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)))),
% 1.07/1.03    inference(definition_unfolding,[],[f87,f91])).
% 1.07/1.03  
% 1.07/1.03  fof(f16,axiom,(
% 1.07/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 1.07/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.07/1.03  
% 1.07/1.03  fof(f30,plain,(
% 1.07/1.03    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.07/1.03    inference(ennf_transformation,[],[f16])).
% 1.07/1.03  
% 1.07/1.03  fof(f79,plain,(
% 1.07/1.03    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.07/1.03    inference(cnf_transformation,[],[f30])).
% 1.07/1.03  
% 1.07/1.03  fof(f3,axiom,(
% 1.07/1.03    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.07/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.07/1.03  
% 1.07/1.03  fof(f38,plain,(
% 1.07/1.03    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.07/1.03    inference(nnf_transformation,[],[f3])).
% 1.07/1.03  
% 1.07/1.03  fof(f39,plain,(
% 1.07/1.03    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.07/1.03    inference(flattening,[],[f38])).
% 1.07/1.03  
% 1.07/1.03  fof(f40,plain,(
% 1.07/1.03    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.07/1.03    inference(rectify,[],[f39])).
% 1.07/1.03  
% 1.07/1.03  fof(f41,plain,(
% 1.07/1.03    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2))))),
% 1.07/1.03    introduced(choice_axiom,[])).
% 1.07/1.03  
% 1.07/1.03  fof(f42,plain,(
% 1.07/1.03    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.07/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).
% 1.07/1.03  
% 1.07/1.03  fof(f57,plain,(
% 1.07/1.03    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 1.07/1.03    inference(cnf_transformation,[],[f42])).
% 1.07/1.03  
% 1.07/1.03  fof(f95,plain,(
% 1.07/1.03    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 1.07/1.03    inference(definition_unfolding,[],[f57,f90])).
% 1.07/1.03  
% 1.07/1.03  fof(f109,plain,(
% 1.07/1.03    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X4) != X2) )),
% 1.07/1.03    inference(equality_resolution,[],[f95])).
% 1.07/1.03  
% 1.07/1.03  fof(f110,plain,(
% 1.07/1.03    ( ! [X4,X0] : (r2_hidden(X4,k2_enumset1(X0,X0,X0,X4))) )),
% 1.07/1.03    inference(equality_resolution,[],[f109])).
% 1.07/1.03  
% 1.07/1.03  fof(f18,axiom,(
% 1.07/1.03    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 1.07/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.07/1.03  
% 1.07/1.03  fof(f32,plain,(
% 1.07/1.03    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.07/1.03    inference(ennf_transformation,[],[f18])).
% 1.07/1.03  
% 1.07/1.03  fof(f33,plain,(
% 1.07/1.03    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.07/1.03    inference(flattening,[],[f32])).
% 1.07/1.03  
% 1.07/1.03  fof(f84,plain,(
% 1.07/1.03    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.07/1.03    inference(cnf_transformation,[],[f33])).
% 1.07/1.03  
% 1.07/1.03  fof(f86,plain,(
% 1.07/1.03    v1_funct_2(sK4,k1_tarski(sK2),sK3)),
% 1.07/1.03    inference(cnf_transformation,[],[f50])).
% 1.07/1.03  
% 1.07/1.03  fof(f106,plain,(
% 1.07/1.03    v1_funct_2(sK4,k2_enumset1(sK2,sK2,sK2,sK2),sK3)),
% 1.07/1.03    inference(definition_unfolding,[],[f86,f91])).
% 1.07/1.03  
% 1.07/1.03  fof(f85,plain,(
% 1.07/1.03    v1_funct_1(sK4)),
% 1.07/1.03    inference(cnf_transformation,[],[f50])).
% 1.07/1.03  
% 1.07/1.03  fof(f88,plain,(
% 1.07/1.03    k1_xboole_0 != sK3),
% 1.07/1.03    inference(cnf_transformation,[],[f50])).
% 1.07/1.03  
% 1.07/1.03  fof(f17,axiom,(
% 1.07/1.03    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_tarski(X2) = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.07/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.07/1.03  
% 1.07/1.03  fof(f31,plain,(
% 1.07/1.03    ! [X0] : ? [X1] : (! [X2] : (k1_tarski(X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.07/1.03    inference(ennf_transformation,[],[f17])).
% 1.07/1.03  
% 1.07/1.03  fof(f47,plain,(
% 1.07/1.03    ! [X0] : (? [X1] : (! [X2] : (k1_tarski(X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (k1_tarski(X2) = k1_funct_1(sK1(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK1(X0)) = X0 & v1_funct_1(sK1(X0)) & v1_relat_1(sK1(X0))))),
% 1.07/1.03    introduced(choice_axiom,[])).
% 1.07/1.03  
% 1.07/1.03  fof(f48,plain,(
% 1.07/1.03    ! [X0] : (! [X2] : (k1_tarski(X2) = k1_funct_1(sK1(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK1(X0)) = X0 & v1_funct_1(sK1(X0)) & v1_relat_1(sK1(X0)))),
% 1.07/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f47])).
% 1.07/1.03  
% 1.07/1.03  fof(f83,plain,(
% 1.07/1.03    ( ! [X2,X0] : (k1_tarski(X2) = k1_funct_1(sK1(X0),X2) | ~r2_hidden(X2,X0)) )),
% 1.07/1.03    inference(cnf_transformation,[],[f48])).
% 1.07/1.03  
% 1.07/1.03  fof(f103,plain,(
% 1.07/1.03    ( ! [X2,X0] : (k2_enumset1(X2,X2,X2,X2) = k1_funct_1(sK1(X0),X2) | ~r2_hidden(X2,X0)) )),
% 1.07/1.03    inference(definition_unfolding,[],[f83,f91])).
% 1.07/1.03  
% 1.07/1.03  fof(f8,axiom,(
% 1.07/1.03    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 1.07/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.07/1.03  
% 1.07/1.03  fof(f22,plain,(
% 1.07/1.03    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 1.07/1.03    inference(ennf_transformation,[],[f8])).
% 1.07/1.03  
% 1.07/1.03  fof(f67,plain,(
% 1.07/1.03    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 1.07/1.03    inference(cnf_transformation,[],[f22])).
% 1.07/1.03  
% 1.07/1.03  fof(f101,plain,(
% 1.07/1.03    ( ! [X0,X1] : (m1_subset_1(k2_enumset1(X0,X0,X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 1.07/1.03    inference(definition_unfolding,[],[f67,f91])).
% 1.07/1.03  
% 1.07/1.03  fof(f11,axiom,(
% 1.07/1.03    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.07/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.07/1.03  
% 1.07/1.03  fof(f73,plain,(
% 1.07/1.03    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.07/1.03    inference(cnf_transformation,[],[f11])).
% 1.07/1.03  
% 1.07/1.03  fof(f82,plain,(
% 1.07/1.03    ( ! [X0] : (k1_relat_1(sK1(X0)) = X0) )),
% 1.07/1.03    inference(cnf_transformation,[],[f48])).
% 1.07/1.03  
% 1.07/1.03  fof(f12,axiom,(
% 1.07/1.03    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.07/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.07/1.03  
% 1.07/1.03  fof(f24,plain,(
% 1.07/1.03    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.07/1.03    inference(ennf_transformation,[],[f12])).
% 1.07/1.03  
% 1.07/1.03  fof(f25,plain,(
% 1.07/1.03    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.07/1.03    inference(flattening,[],[f24])).
% 1.07/1.03  
% 1.07/1.03  fof(f74,plain,(
% 1.07/1.03    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.07/1.03    inference(cnf_transformation,[],[f25])).
% 1.07/1.03  
% 1.07/1.03  fof(f80,plain,(
% 1.07/1.03    ( ! [X0] : (v1_relat_1(sK1(X0))) )),
% 1.07/1.03    inference(cnf_transformation,[],[f48])).
% 1.07/1.03  
% 1.07/1.03  fof(f15,axiom,(
% 1.07/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.07/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.07/1.03  
% 1.07/1.03  fof(f21,plain,(
% 1.07/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.07/1.03    inference(pure_predicate_removal,[],[f15])).
% 1.07/1.03  
% 1.07/1.03  fof(f29,plain,(
% 1.07/1.03    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.07/1.03    inference(ennf_transformation,[],[f21])).
% 1.07/1.03  
% 1.07/1.03  fof(f78,plain,(
% 1.07/1.03    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.07/1.03    inference(cnf_transformation,[],[f29])).
% 1.07/1.03  
% 1.07/1.03  fof(f10,axiom,(
% 1.07/1.03    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.07/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.07/1.03  
% 1.07/1.03  fof(f23,plain,(
% 1.07/1.03    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.07/1.03    inference(ennf_transformation,[],[f10])).
% 1.07/1.03  
% 1.07/1.03  fof(f46,plain,(
% 1.07/1.03    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.07/1.03    inference(nnf_transformation,[],[f23])).
% 1.07/1.03  
% 1.07/1.03  fof(f70,plain,(
% 1.07/1.03    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.07/1.03    inference(cnf_transformation,[],[f46])).
% 1.07/1.03  
% 1.07/1.03  fof(f14,axiom,(
% 1.07/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.07/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.07/1.03  
% 1.07/1.03  fof(f28,plain,(
% 1.07/1.03    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.07/1.03    inference(ennf_transformation,[],[f14])).
% 1.07/1.03  
% 1.07/1.03  fof(f77,plain,(
% 1.07/1.03    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.07/1.03    inference(cnf_transformation,[],[f28])).
% 1.07/1.03  
% 1.07/1.03  fof(f7,axiom,(
% 1.07/1.03    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.07/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.07/1.03  
% 1.07/1.03  fof(f43,plain,(
% 1.07/1.03    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.07/1.03    inference(nnf_transformation,[],[f7])).
% 1.07/1.03  
% 1.07/1.03  fof(f44,plain,(
% 1.07/1.03    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.07/1.03    inference(flattening,[],[f43])).
% 1.07/1.03  
% 1.07/1.03  fof(f64,plain,(
% 1.07/1.03    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.07/1.03    inference(cnf_transformation,[],[f44])).
% 1.07/1.03  
% 1.07/1.03  fof(f100,plain,(
% 1.07/1.03    ( ! [X0,X1] : (k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))) )),
% 1.07/1.03    inference(definition_unfolding,[],[f64,f91,f91])).
% 1.07/1.03  
% 1.07/1.03  fof(f89,plain,(
% 1.07/1.03    k1_tarski(k1_funct_1(sK4,sK2)) != k2_relset_1(k1_tarski(sK2),sK3,sK4)),
% 1.07/1.03    inference(cnf_transformation,[],[f50])).
% 1.07/1.03  
% 1.07/1.03  fof(f104,plain,(
% 1.07/1.03    k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) != k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4)),
% 1.07/1.03    inference(definition_unfolding,[],[f89,f91,f91])).
% 1.07/1.03  
% 1.07/1.03  fof(f13,axiom,(
% 1.07/1.03    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 1.07/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.07/1.03  
% 1.07/1.03  fof(f26,plain,(
% 1.07/1.03    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.07/1.03    inference(ennf_transformation,[],[f13])).
% 1.07/1.03  
% 1.07/1.03  fof(f27,plain,(
% 1.07/1.03    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.07/1.03    inference(flattening,[],[f26])).
% 1.07/1.03  
% 1.07/1.03  fof(f76,plain,(
% 1.07/1.03    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.07/1.03    inference(cnf_transformation,[],[f27])).
% 1.07/1.03  
% 1.07/1.03  fof(f102,plain,(
% 1.07/1.03    ( ! [X0,X1] : (k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1) | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.07/1.03    inference(definition_unfolding,[],[f76,f91,f91])).
% 1.07/1.03  
% 1.07/1.03  fof(f9,axiom,(
% 1.07/1.03    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.07/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.07/1.03  
% 1.07/1.03  fof(f45,plain,(
% 1.07/1.03    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.07/1.03    inference(nnf_transformation,[],[f9])).
% 1.07/1.03  
% 1.07/1.03  fof(f68,plain,(
% 1.07/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.07/1.03    inference(cnf_transformation,[],[f45])).
% 1.07/1.03  
% 1.07/1.03  fof(f2,axiom,(
% 1.07/1.03    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.07/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.07/1.03  
% 1.07/1.03  fof(f54,plain,(
% 1.07/1.03    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.07/1.03    inference(cnf_transformation,[],[f2])).
% 1.07/1.03  
% 1.07/1.03  fof(f1,axiom,(
% 1.07/1.03    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.07/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.07/1.03  
% 1.07/1.03  fof(f36,plain,(
% 1.07/1.03    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.07/1.03    inference(nnf_transformation,[],[f1])).
% 1.07/1.03  
% 1.07/1.03  fof(f37,plain,(
% 1.07/1.03    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.07/1.03    inference(flattening,[],[f36])).
% 1.07/1.03  
% 1.07/1.03  fof(f53,plain,(
% 1.07/1.03    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.07/1.03    inference(cnf_transformation,[],[f37])).
% 1.07/1.03  
% 1.07/1.03  fof(f56,plain,(
% 1.07/1.03    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 1.07/1.03    inference(cnf_transformation,[],[f42])).
% 1.07/1.03  
% 1.07/1.03  fof(f96,plain,(
% 1.07/1.03    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 1.07/1.03    inference(definition_unfolding,[],[f56,f90])).
% 1.07/1.03  
% 1.07/1.03  fof(f111,plain,(
% 1.07/1.03    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_enumset1(X4,X4,X4,X1) != X2) )),
% 1.07/1.03    inference(equality_resolution,[],[f96])).
% 1.07/1.03  
% 1.07/1.03  fof(f112,plain,(
% 1.07/1.03    ( ! [X4,X1] : (r2_hidden(X4,k2_enumset1(X4,X4,X4,X1))) )),
% 1.07/1.03    inference(equality_resolution,[],[f111])).
% 1.07/1.03  
% 1.07/1.03  cnf(c_33,negated_conjecture,
% 1.07/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) ),
% 1.07/1.03      inference(cnf_transformation,[],[f105]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_1915,plain,
% 1.07/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) = iProver_top ),
% 1.07/1.03      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_25,plain,
% 1.07/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.07/1.03      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 1.07/1.03      inference(cnf_transformation,[],[f79]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_1919,plain,
% 1.07/1.03      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 1.07/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 1.07/1.03      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_4288,plain,
% 1.07/1.03      ( k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) = k2_relat_1(sK4) ),
% 1.07/1.03      inference(superposition,[status(thm)],[c_1915,c_1919]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_7,plain,
% 1.07/1.03      ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) ),
% 1.07/1.03      inference(cnf_transformation,[],[f110]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_1932,plain,
% 1.07/1.03      ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) = iProver_top ),
% 1.07/1.03      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_30,plain,
% 1.07/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 1.07/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.07/1.03      | ~ r2_hidden(X3,X1)
% 1.07/1.03      | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
% 1.07/1.03      | ~ v1_funct_1(X0)
% 1.07/1.03      | k1_xboole_0 = X2 ),
% 1.07/1.03      inference(cnf_transformation,[],[f84]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_34,negated_conjecture,
% 1.07/1.03      ( v1_funct_2(sK4,k2_enumset1(sK2,sK2,sK2,sK2),sK3) ),
% 1.07/1.03      inference(cnf_transformation,[],[f106]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_414,plain,
% 1.07/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.07/1.03      | ~ r2_hidden(X3,X1)
% 1.07/1.03      | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
% 1.07/1.03      | ~ v1_funct_1(X0)
% 1.07/1.03      | k2_enumset1(sK2,sK2,sK2,sK2) != X1
% 1.07/1.03      | sK3 != X2
% 1.07/1.03      | sK4 != X0
% 1.07/1.03      | k1_xboole_0 = X2 ),
% 1.07/1.03      inference(resolution_lifted,[status(thm)],[c_30,c_34]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_415,plain,
% 1.07/1.03      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)))
% 1.07/1.03      | ~ r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2))
% 1.07/1.03      | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4))
% 1.07/1.03      | ~ v1_funct_1(sK4)
% 1.07/1.03      | k1_xboole_0 = sK3 ),
% 1.07/1.03      inference(unflattening,[status(thm)],[c_414]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_35,negated_conjecture,
% 1.07/1.03      ( v1_funct_1(sK4) ),
% 1.07/1.03      inference(cnf_transformation,[],[f85]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_32,negated_conjecture,
% 1.07/1.03      ( k1_xboole_0 != sK3 ),
% 1.07/1.03      inference(cnf_transformation,[],[f88]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_419,plain,
% 1.07/1.03      ( ~ r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2))
% 1.07/1.03      | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4)) ),
% 1.07/1.03      inference(global_propositional_subsumption,
% 1.07/1.03                [status(thm)],
% 1.07/1.03                [c_415,c_35,c_33,c_32]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_1913,plain,
% 1.07/1.03      ( r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
% 1.07/1.03      | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4)) = iProver_top ),
% 1.07/1.03      inference(predicate_to_equality,[status(thm)],[c_419]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_26,plain,
% 1.07/1.03      ( ~ r2_hidden(X0,X1)
% 1.07/1.03      | k2_enumset1(X0,X0,X0,X0) = k1_funct_1(sK1(X1),X0) ),
% 1.07/1.03      inference(cnf_transformation,[],[f103]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_1918,plain,
% 1.07/1.03      ( k2_enumset1(X0,X0,X0,X0) = k1_funct_1(sK1(X1),X0)
% 1.07/1.03      | r2_hidden(X0,X1) != iProver_top ),
% 1.07/1.03      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_3063,plain,
% 1.07/1.03      ( k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k1_funct_1(sK1(k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4)),k1_funct_1(sK4,X0))
% 1.07/1.03      | r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top ),
% 1.07/1.03      inference(superposition,[status(thm)],[c_1913,c_1918]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_3254,plain,
% 1.07/1.03      ( k1_funct_1(sK1(k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4)),k1_funct_1(sK4,sK2)) = k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) ),
% 1.07/1.03      inference(superposition,[status(thm)],[c_1932,c_3063]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_4475,plain,
% 1.07/1.03      ( k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) = k1_funct_1(sK1(k2_relat_1(sK4)),k1_funct_1(sK4,sK2)) ),
% 1.07/1.03      inference(demodulation,[status(thm)],[c_4288,c_3254]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_13,plain,
% 1.07/1.03      ( m1_subset_1(k2_enumset1(X0,X0,X0,X0),k1_zfmisc_1(X1))
% 1.07/1.03      | ~ r2_hidden(X0,X1) ),
% 1.07/1.03      inference(cnf_transformation,[],[f101]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_1926,plain,
% 1.07/1.03      ( m1_subset_1(k2_enumset1(X0,X0,X0,X0),k1_zfmisc_1(X1)) = iProver_top
% 1.07/1.03      | r2_hidden(X0,X1) != iProver_top ),
% 1.07/1.03      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_4811,plain,
% 1.07/1.03      ( m1_subset_1(k1_funct_1(sK1(k2_relat_1(sK4)),k1_funct_1(sK4,sK2)),k1_zfmisc_1(X0)) = iProver_top
% 1.07/1.03      | r2_hidden(k1_funct_1(sK4,sK2),X0) != iProver_top ),
% 1.07/1.03      inference(superposition,[status(thm)],[c_4475,c_1926]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_18,plain,
% 1.07/1.03      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 1.07/1.03      inference(cnf_transformation,[],[f73]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_27,plain,
% 1.07/1.03      ( k1_relat_1(sK1(X0)) = X0 ),
% 1.07/1.03      inference(cnf_transformation,[],[f82]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_21,plain,
% 1.07/1.03      ( ~ v1_relat_1(X0)
% 1.07/1.03      | k1_relat_1(X0) != k1_xboole_0
% 1.07/1.03      | k1_xboole_0 = X0 ),
% 1.07/1.03      inference(cnf_transformation,[],[f74]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_1922,plain,
% 1.07/1.03      ( k1_relat_1(X0) != k1_xboole_0
% 1.07/1.03      | k1_xboole_0 = X0
% 1.07/1.03      | v1_relat_1(X0) != iProver_top ),
% 1.07/1.03      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_3191,plain,
% 1.07/1.03      ( sK1(X0) = k1_xboole_0
% 1.07/1.03      | k1_xboole_0 != X0
% 1.07/1.03      | v1_relat_1(sK1(X0)) != iProver_top ),
% 1.07/1.03      inference(superposition,[status(thm)],[c_27,c_1922]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_29,plain,
% 1.07/1.03      ( v1_relat_1(sK1(X0)) ),
% 1.07/1.03      inference(cnf_transformation,[],[f80]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_42,plain,
% 1.07/1.03      ( v1_relat_1(sK1(X0)) = iProver_top ),
% 1.07/1.03      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_3245,plain,
% 1.07/1.03      ( k1_xboole_0 != X0 | sK1(X0) = k1_xboole_0 ),
% 1.07/1.03      inference(global_propositional_subsumption,
% 1.07/1.03                [status(thm)],
% 1.07/1.03                [c_3191,c_42]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_3246,plain,
% 1.07/1.03      ( sK1(X0) = k1_xboole_0 | k1_xboole_0 != X0 ),
% 1.07/1.03      inference(renaming,[status(thm)],[c_3245]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_3250,plain,
% 1.07/1.03      ( sK1(k1_xboole_0) = k1_xboole_0 ),
% 1.07/1.03      inference(equality_resolution,[status(thm)],[c_3246]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_24,plain,
% 1.07/1.03      ( v4_relat_1(X0,X1)
% 1.07/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 1.07/1.03      inference(cnf_transformation,[],[f78]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_17,plain,
% 1.07/1.03      ( ~ v4_relat_1(X0,X1)
% 1.07/1.03      | r1_tarski(k1_relat_1(X0),X1)
% 1.07/1.03      | ~ v1_relat_1(X0) ),
% 1.07/1.03      inference(cnf_transformation,[],[f70]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_469,plain,
% 1.07/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.07/1.03      | r1_tarski(k1_relat_1(X0),X1)
% 1.07/1.03      | ~ v1_relat_1(X0) ),
% 1.07/1.03      inference(resolution,[status(thm)],[c_24,c_17]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_23,plain,
% 1.07/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.07/1.03      | v1_relat_1(X0) ),
% 1.07/1.03      inference(cnf_transformation,[],[f77]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_473,plain,
% 1.07/1.03      ( r1_tarski(k1_relat_1(X0),X1)
% 1.07/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 1.07/1.03      inference(global_propositional_subsumption,
% 1.07/1.03                [status(thm)],
% 1.07/1.03                [c_469,c_23]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_474,plain,
% 1.07/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.07/1.03      | r1_tarski(k1_relat_1(X0),X1) ),
% 1.07/1.03      inference(renaming,[status(thm)],[c_473]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_1912,plain,
% 1.07/1.03      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 1.07/1.03      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 1.07/1.03      inference(predicate_to_equality,[status(thm)],[c_474]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_2264,plain,
% 1.07/1.03      ( r1_tarski(k1_relat_1(sK4),k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
% 1.07/1.03      inference(superposition,[status(thm)],[c_1915,c_1912]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_12,plain,
% 1.07/1.03      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
% 1.07/1.03      | k2_enumset1(X1,X1,X1,X1) = X0
% 1.07/1.03      | k1_xboole_0 = X0 ),
% 1.07/1.03      inference(cnf_transformation,[],[f100]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_1927,plain,
% 1.07/1.03      ( k2_enumset1(X0,X0,X0,X0) = X1
% 1.07/1.03      | k1_xboole_0 = X1
% 1.07/1.03      | r1_tarski(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
% 1.07/1.03      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_4427,plain,
% 1.07/1.03      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_relat_1(sK4)
% 1.07/1.03      | k1_relat_1(sK4) = k1_xboole_0 ),
% 1.07/1.03      inference(superposition,[status(thm)],[c_2264,c_1927]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_38,plain,
% 1.07/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) = iProver_top ),
% 1.07/1.03      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_31,negated_conjecture,
% 1.07/1.03      ( k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) != k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) ),
% 1.07/1.03      inference(cnf_transformation,[],[f104]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_22,plain,
% 1.07/1.03      ( ~ v1_funct_1(X0)
% 1.07/1.03      | ~ v1_relat_1(X0)
% 1.07/1.03      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 1.07/1.03      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
% 1.07/1.03      inference(cnf_transformation,[],[f102]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_449,plain,
% 1.07/1.03      ( ~ v1_relat_1(X0)
% 1.07/1.03      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 1.07/1.03      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
% 1.07/1.03      | sK4 != X0 ),
% 1.07/1.03      inference(resolution_lifted,[status(thm)],[c_22,c_35]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_450,plain,
% 1.07/1.03      ( ~ v1_relat_1(sK4)
% 1.07/1.03      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK4)
% 1.07/1.03      | k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k2_relat_1(sK4) ),
% 1.07/1.03      inference(unflattening,[status(thm)],[c_449]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_451,plain,
% 1.07/1.03      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK4)
% 1.07/1.03      | k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k2_relat_1(sK4)
% 1.07/1.03      | v1_relat_1(sK4) != iProver_top ),
% 1.07/1.03      inference(predicate_to_equality,[status(thm)],[c_450]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_453,plain,
% 1.07/1.03      ( k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) = k2_relat_1(sK4)
% 1.07/1.03      | k2_enumset1(sK2,sK2,sK2,sK2) != k1_relat_1(sK4)
% 1.07/1.03      | v1_relat_1(sK4) != iProver_top ),
% 1.07/1.03      inference(instantiation,[status(thm)],[c_451]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_2119,plain,
% 1.07/1.03      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)))
% 1.07/1.03      | v1_relat_1(sK4) ),
% 1.07/1.03      inference(instantiation,[status(thm)],[c_23]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_2120,plain,
% 1.07/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) != iProver_top
% 1.07/1.03      | v1_relat_1(sK4) = iProver_top ),
% 1.07/1.03      inference(predicate_to_equality,[status(thm)],[c_2119]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_2170,plain,
% 1.07/1.03      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)))
% 1.07/1.03      | k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) = k2_relat_1(sK4) ),
% 1.07/1.03      inference(instantiation,[status(thm)],[c_25]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_1271,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_2152,plain,
% 1.07/1.03      ( k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) != X0
% 1.07/1.03      | k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) = k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4)
% 1.07/1.03      | k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) != X0 ),
% 1.07/1.03      inference(instantiation,[status(thm)],[c_1271]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_2380,plain,
% 1.07/1.03      ( k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) = k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4)
% 1.07/1.03      | k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) != k2_relat_1(sK4)
% 1.07/1.03      | k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) != k2_relat_1(sK4) ),
% 1.07/1.03      inference(instantiation,[status(thm)],[c_2152]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_5319,plain,
% 1.07/1.03      ( k1_relat_1(sK4) = k1_xboole_0 ),
% 1.07/1.03      inference(global_propositional_subsumption,
% 1.07/1.03                [status(thm)],
% 1.07/1.03                [c_4427,c_33,c_38,c_31,c_453,c_2120,c_2170,c_2380]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_5328,plain,
% 1.07/1.03      ( sK4 = k1_xboole_0 | v1_relat_1(sK4) != iProver_top ),
% 1.07/1.03      inference(superposition,[status(thm)],[c_5319,c_1922]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_5375,plain,
% 1.07/1.03      ( sK4 = k1_xboole_0 ),
% 1.07/1.03      inference(global_propositional_subsumption,
% 1.07/1.03                [status(thm)],
% 1.07/1.03                [c_5328,c_38,c_2120]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_6298,plain,
% 1.07/1.03      ( m1_subset_1(k1_funct_1(k1_xboole_0,k1_funct_1(k1_xboole_0,sK2)),k1_zfmisc_1(X0)) = iProver_top
% 1.07/1.03      | r2_hidden(k1_funct_1(k1_xboole_0,sK2),X0) != iProver_top ),
% 1.07/1.03      inference(light_normalisation,
% 1.07/1.03                [status(thm)],
% 1.07/1.03                [c_4811,c_18,c_3250,c_5375]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_15,plain,
% 1.07/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 1.07/1.03      inference(cnf_transformation,[],[f68]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_1924,plain,
% 1.07/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 1.07/1.03      | r1_tarski(X0,X1) = iProver_top ),
% 1.07/1.03      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_6304,plain,
% 1.07/1.03      ( r2_hidden(k1_funct_1(k1_xboole_0,sK2),X0) != iProver_top
% 1.07/1.03      | r1_tarski(k1_funct_1(k1_xboole_0,k1_funct_1(k1_xboole_0,sK2)),X0) = iProver_top ),
% 1.07/1.03      inference(superposition,[status(thm)],[c_6298,c_1924]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_3,plain,
% 1.07/1.03      ( r1_tarski(k1_xboole_0,X0) ),
% 1.07/1.03      inference(cnf_transformation,[],[f54]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_1936,plain,
% 1.07/1.03      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 1.07/1.03      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_0,plain,
% 1.07/1.03      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 1.07/1.03      inference(cnf_transformation,[],[f53]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_1938,plain,
% 1.07/1.03      ( X0 = X1
% 1.07/1.03      | r1_tarski(X0,X1) != iProver_top
% 1.07/1.03      | r1_tarski(X1,X0) != iProver_top ),
% 1.07/1.03      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_4310,plain,
% 1.07/1.03      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 1.07/1.03      inference(superposition,[status(thm)],[c_1936,c_1938]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_7623,plain,
% 1.07/1.03      ( k1_funct_1(k1_xboole_0,k1_funct_1(k1_xboole_0,sK2)) = k1_xboole_0
% 1.07/1.03      | r2_hidden(k1_funct_1(k1_xboole_0,sK2),k1_xboole_0) != iProver_top ),
% 1.07/1.03      inference(superposition,[status(thm)],[c_6304,c_4310]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_4477,plain,
% 1.07/1.03      ( r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
% 1.07/1.03      | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top ),
% 1.07/1.03      inference(demodulation,[status(thm)],[c_4288,c_1913]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_5384,plain,
% 1.07/1.03      ( r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
% 1.07/1.03      | r2_hidden(k1_funct_1(k1_xboole_0,X0),k2_relat_1(k1_xboole_0)) = iProver_top ),
% 1.07/1.03      inference(demodulation,[status(thm)],[c_5375,c_4477]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_5406,plain,
% 1.07/1.03      ( r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
% 1.07/1.03      | r2_hidden(k1_funct_1(k1_xboole_0,X0),k1_xboole_0) = iProver_top ),
% 1.07/1.03      inference(light_normalisation,[status(thm)],[c_5384,c_18]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_5431,plain,
% 1.07/1.03      ( r2_hidden(k1_funct_1(k1_xboole_0,sK2),k1_xboole_0) = iProver_top
% 1.07/1.03      | r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top ),
% 1.07/1.03      inference(instantiation,[status(thm)],[c_5406]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_3376,plain,
% 1.07/1.03      ( k1_funct_1(sK1(k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4)),k1_funct_1(sK4,sK2)) != k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) ),
% 1.07/1.03      inference(demodulation,[status(thm)],[c_3254,c_31]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_4474,plain,
% 1.07/1.03      ( k1_funct_1(sK1(k2_relat_1(sK4)),k1_funct_1(sK4,sK2)) != k2_relat_1(sK4) ),
% 1.07/1.03      inference(demodulation,[status(thm)],[c_4288,c_3376]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_5386,plain,
% 1.07/1.03      ( k1_funct_1(sK1(k2_relat_1(k1_xboole_0)),k1_funct_1(k1_xboole_0,sK2)) != k2_relat_1(k1_xboole_0) ),
% 1.07/1.03      inference(demodulation,[status(thm)],[c_5375,c_4474]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_5399,plain,
% 1.07/1.03      ( k1_funct_1(k1_xboole_0,k1_funct_1(k1_xboole_0,sK2)) != k1_xboole_0 ),
% 1.07/1.03      inference(light_normalisation,[status(thm)],[c_5386,c_18,c_3250]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_8,plain,
% 1.07/1.03      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
% 1.07/1.03      inference(cnf_transformation,[],[f112]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_97,plain,
% 1.07/1.03      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
% 1.07/1.03      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_99,plain,
% 1.07/1.03      ( r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
% 1.07/1.03      inference(instantiation,[status(thm)],[c_97]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(contradiction,plain,
% 1.07/1.03      ( $false ),
% 1.07/1.03      inference(minisat,[status(thm)],[c_7623,c_5431,c_5399,c_99]) ).
% 1.07/1.03  
% 1.07/1.03  
% 1.07/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 1.07/1.03  
% 1.07/1.03  ------                               Statistics
% 1.07/1.03  
% 1.07/1.03  ------ General
% 1.07/1.03  
% 1.07/1.03  abstr_ref_over_cycles:                  0
% 1.07/1.03  abstr_ref_under_cycles:                 0
% 1.07/1.03  gc_basic_clause_elim:                   0
% 1.07/1.03  forced_gc_time:                         0
% 1.07/1.03  parsing_time:                           0.009
% 1.07/1.03  unif_index_cands_time:                  0.
% 1.07/1.03  unif_index_add_time:                    0.
% 1.07/1.03  orderings_time:                         0.
% 1.07/1.03  out_proof_time:                         0.027
% 1.07/1.03  total_time:                             0.309
% 1.07/1.03  num_of_symbols:                         51
% 1.07/1.03  num_of_terms:                           7911
% 1.07/1.03  
% 1.07/1.03  ------ Preprocessing
% 1.07/1.03  
% 1.07/1.03  num_of_splits:                          0
% 1.07/1.03  num_of_split_atoms:                     0
% 1.07/1.03  num_of_reused_defs:                     0
% 1.07/1.03  num_eq_ax_congr_red:                    14
% 1.07/1.03  num_of_sem_filtered_clauses:            1
% 1.07/1.03  num_of_subtypes:                        0
% 1.07/1.03  monotx_restored_types:                  0
% 1.07/1.03  sat_num_of_epr_types:                   0
% 1.07/1.03  sat_num_of_non_cyclic_types:            0
% 1.07/1.03  sat_guarded_non_collapsed_types:        0
% 1.07/1.03  num_pure_diseq_elim:                    0
% 1.07/1.03  simp_replaced_by:                       0
% 1.07/1.03  res_preprocessed:                       160
% 1.07/1.03  prep_upred:                             0
% 1.07/1.03  prep_unflattend:                        35
% 1.07/1.03  smt_new_axioms:                         0
% 1.07/1.03  pred_elim_cands:                        5
% 1.07/1.03  pred_elim:                              2
% 1.07/1.03  pred_elim_cl:                           3
% 1.07/1.03  pred_elim_cycles:                       8
% 1.07/1.03  merged_defs:                            8
% 1.07/1.03  merged_defs_ncl:                        0
% 1.07/1.03  bin_hyper_res:                          8
% 1.07/1.03  prep_cycles:                            4
% 1.07/1.03  pred_elim_time:                         0.011
% 1.07/1.03  splitting_time:                         0.
% 1.07/1.03  sem_filter_time:                        0.
% 1.07/1.03  monotx_time:                            0.
% 1.07/1.03  subtype_inf_time:                       0.
% 1.07/1.03  
% 1.07/1.03  ------ Problem properties
% 1.07/1.03  
% 1.07/1.03  clauses:                                32
% 1.07/1.03  conjectures:                            4
% 1.07/1.03  epr:                                    5
% 1.07/1.03  horn:                                   29
% 1.07/1.03  ground:                                 6
% 1.07/1.03  unary:                                  15
% 1.07/1.03  binary:                                 8
% 1.07/1.03  lits:                                   60
% 1.07/1.03  lits_eq:                                25
% 1.07/1.03  fd_pure:                                0
% 1.07/1.03  fd_pseudo:                              0
% 1.07/1.03  fd_cond:                                2
% 1.07/1.03  fd_pseudo_cond:                         5
% 1.07/1.03  ac_symbols:                             0
% 1.07/1.03  
% 1.07/1.03  ------ Propositional Solver
% 1.07/1.03  
% 1.07/1.03  prop_solver_calls:                      27
% 1.07/1.03  prop_fast_solver_calls:                 975
% 1.07/1.03  smt_solver_calls:                       0
% 1.07/1.03  smt_fast_solver_calls:                  0
% 1.07/1.03  prop_num_of_clauses:                    2797
% 1.07/1.03  prop_preprocess_simplified:             9489
% 1.07/1.03  prop_fo_subsumed:                       12
% 1.07/1.03  prop_solver_time:                       0.
% 1.07/1.03  smt_solver_time:                        0.
% 1.07/1.03  smt_fast_solver_time:                   0.
% 1.07/1.03  prop_fast_solver_time:                  0.
% 1.07/1.03  prop_unsat_core_time:                   0.
% 1.07/1.03  
% 1.07/1.03  ------ QBF
% 1.07/1.03  
% 1.07/1.03  qbf_q_res:                              0
% 1.07/1.03  qbf_num_tautologies:                    0
% 1.07/1.03  qbf_prep_cycles:                        0
% 1.07/1.03  
% 1.07/1.03  ------ BMC1
% 1.07/1.03  
% 1.07/1.03  bmc1_current_bound:                     -1
% 1.07/1.03  bmc1_last_solved_bound:                 -1
% 1.07/1.03  bmc1_unsat_core_size:                   -1
% 1.07/1.03  bmc1_unsat_core_parents_size:           -1
% 1.07/1.03  bmc1_merge_next_fun:                    0
% 1.07/1.03  bmc1_unsat_core_clauses_time:           0.
% 1.07/1.03  
% 1.07/1.03  ------ Instantiation
% 1.07/1.03  
% 1.07/1.03  inst_num_of_clauses:                    814
% 1.07/1.03  inst_num_in_passive:                    424
% 1.07/1.03  inst_num_in_active:                     378
% 1.07/1.03  inst_num_in_unprocessed:                13
% 1.07/1.03  inst_num_of_loops:                      400
% 1.07/1.03  inst_num_of_learning_restarts:          0
% 1.07/1.03  inst_num_moves_active_passive:          21
% 1.07/1.03  inst_lit_activity:                      0
% 1.07/1.03  inst_lit_activity_moves:                0
% 1.07/1.03  inst_num_tautologies:                   0
% 1.07/1.03  inst_num_prop_implied:                  0
% 1.07/1.03  inst_num_existing_simplified:           0
% 1.07/1.03  inst_num_eq_res_simplified:             0
% 1.07/1.03  inst_num_child_elim:                    0
% 1.07/1.03  inst_num_of_dismatching_blockings:      356
% 1.07/1.03  inst_num_of_non_proper_insts:           785
% 1.07/1.03  inst_num_of_duplicates:                 0
% 1.07/1.03  inst_inst_num_from_inst_to_res:         0
% 1.07/1.03  inst_dismatching_checking_time:         0.
% 1.07/1.03  
% 1.07/1.03  ------ Resolution
% 1.07/1.03  
% 1.07/1.03  res_num_of_clauses:                     0
% 1.07/1.03  res_num_in_passive:                     0
% 1.07/1.03  res_num_in_active:                      0
% 1.07/1.03  res_num_of_loops:                       164
% 1.07/1.03  res_forward_subset_subsumed:            87
% 1.07/1.03  res_backward_subset_subsumed:           2
% 1.07/1.03  res_forward_subsumed:                   0
% 1.07/1.03  res_backward_subsumed:                  0
% 1.07/1.03  res_forward_subsumption_resolution:     0
% 1.07/1.03  res_backward_subsumption_resolution:    0
% 1.07/1.03  res_clause_to_clause_subsumption:       278
% 1.07/1.03  res_orphan_elimination:                 0
% 1.07/1.03  res_tautology_del:                      57
% 1.07/1.03  res_num_eq_res_simplified:              0
% 1.07/1.03  res_num_sel_changes:                    0
% 1.07/1.03  res_moves_from_active_to_pass:          0
% 1.07/1.03  
% 1.07/1.03  ------ Superposition
% 1.07/1.03  
% 1.07/1.03  sup_time_total:                         0.
% 1.07/1.03  sup_time_generating:                    0.
% 1.07/1.03  sup_time_sim_full:                      0.
% 1.07/1.03  sup_time_sim_immed:                     0.
% 1.07/1.03  
% 1.07/1.03  sup_num_of_clauses:                     97
% 1.07/1.03  sup_num_in_active:                      57
% 1.07/1.03  sup_num_in_passive:                     40
% 1.07/1.03  sup_num_of_loops:                       79
% 1.07/1.03  sup_fw_superposition:                   58
% 1.07/1.03  sup_bw_superposition:                   59
% 1.07/1.03  sup_immediate_simplified:               20
% 1.07/1.03  sup_given_eliminated:                   0
% 1.07/1.03  comparisons_done:                       0
% 1.07/1.03  comparisons_avoided:                    4
% 1.07/1.03  
% 1.07/1.03  ------ Simplifications
% 1.07/1.03  
% 1.07/1.03  
% 1.07/1.03  sim_fw_subset_subsumed:                 1
% 1.07/1.03  sim_bw_subset_subsumed:                 0
% 1.07/1.03  sim_fw_subsumed:                        5
% 1.07/1.03  sim_bw_subsumed:                        0
% 1.07/1.03  sim_fw_subsumption_res:                 2
% 1.07/1.03  sim_bw_subsumption_res:                 0
% 1.07/1.03  sim_tautology_del:                      1
% 1.07/1.03  sim_eq_tautology_del:                   12
% 1.07/1.03  sim_eq_res_simp:                        0
% 1.07/1.03  sim_fw_demodulated:                     3
% 1.07/1.03  sim_bw_demodulated:                     23
% 1.07/1.03  sim_light_normalised:                   25
% 1.07/1.03  sim_joinable_taut:                      0
% 1.07/1.03  sim_joinable_simp:                      0
% 1.07/1.03  sim_ac_normalised:                      0
% 1.07/1.03  sim_smt_subsumption:                    0
% 1.07/1.03  
%------------------------------------------------------------------------------
