%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:08 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :  173 (2820 expanded)
%              Number of clauses        :   87 ( 517 expanded)
%              Number of leaves         :   24 ( 771 expanded)
%              Depth                    :   23
%              Number of atoms          :  538 (7229 expanded)
%              Number of equality atoms :  310 (4276 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f44])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f117,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f61])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f40])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f42])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f38,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f39,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f55,plain,
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

fof(f56,plain,
    ( k1_tarski(k1_funct_1(sK5,sK3)) != k2_relset_1(k1_tarski(sK3),sK4,sK5)
    & k1_xboole_0 != sK4
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4)))
    & v1_funct_2(sK5,k1_tarski(sK3),sK4)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f39,f55])).

fof(f99,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4))) ),
    inference(cnf_transformation,[],[f56])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f102,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f64,f65])).

fof(f103,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f63,f102])).

fof(f115,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) ),
    inference(definition_unfolding,[],[f99,f103])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
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

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

fof(f66,plain,(
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
    inference(cnf_transformation,[],[f47])).

fof(f112,plain,(
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
    inference(definition_unfolding,[],[f66,f65,f102,f102,f102,f103,f103,f103,f65])).

fof(f101,plain,(
    k1_tarski(k1_funct_1(sK5,sK3)) != k2_relset_1(k1_tarski(sK3),sK4,sK5) ),
    inference(cnf_transformation,[],[f56])).

fof(f114,plain,(
    k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) ),
    inference(definition_unfolding,[],[f101,f103,f103])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f113,plain,(
    ! [X0,X1] :
      ( k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f83,f103,f103])).

fof(f97,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f56])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f81,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f18,axiom,(
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
    inference(ennf_transformation,[],[f18])).

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

fof(f54,plain,(
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

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f98,plain,(
    v1_funct_2(sK5,k1_tarski(sK3),sK4) ),
    inference(cnf_transformation,[],[f56])).

fof(f116,plain,(
    v1_funct_2(sK5,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
    inference(definition_unfolding,[],[f98,f103])).

fof(f100,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f56])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f50,plain,(
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
    inference(rectify,[],[f49])).

fof(f52,plain,(
    ! [X2,X1] :
      ( ? [X5] :
          ( ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X2)
          & r2_hidden(X5,X1) )
     => ( ! [X6] : ~ r2_hidden(k4_tarski(sK2(X1,X2),X6),X2)
        & r2_hidden(sK2(X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X3,X2] :
      ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
     => r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ( ! [X6] : ~ r2_hidden(k4_tarski(sK2(X1,X2),X6),X2)
            & r2_hidden(sK2(X1,X2),X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f50,f52,f51])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2)
      | ~ r2_hidden(X3,X1)
      | k1_relset_1(X1,X0,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f10,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f62,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f80,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_1337,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1340,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1339,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3102,plain,
    ( r2_hidden(sK0(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1340,c_1339])).

cnf(c_39,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_1317,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_26,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_18,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_434,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_26,c_18])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_438,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_434,c_25])).

cnf(c_439,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_438])).

cnf(c_1315,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_439])).

cnf(c_1630,plain,
    ( r1_tarski(k1_relat_1(sK5),k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1317,c_1315])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X2,X3))
    | k2_enumset1(X1,X1,X2,X3) = X0
    | k2_enumset1(X1,X1,X1,X3) = X0
    | k2_enumset1(X2,X2,X2,X3) = X0
    | k2_enumset1(X1,X1,X1,X2) = X0
    | k2_enumset1(X3,X3,X3,X3) = X0
    | k2_enumset1(X2,X2,X2,X2) = X0
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1328,plain,
    ( k2_enumset1(X0,X0,X1,X2) = X3
    | k2_enumset1(X0,X0,X0,X2) = X3
    | k2_enumset1(X1,X1,X1,X2) = X3
    | k2_enumset1(X0,X0,X0,X1) = X3
    | k2_enumset1(X2,X2,X2,X2) = X3
    | k2_enumset1(X1,X1,X1,X1) = X3
    | k2_enumset1(X0,X0,X0,X0) = X3
    | k1_xboole_0 = X3
    | r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3586,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_relat_1(sK5)
    | k1_relat_1(sK5) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1630,c_1328])).

cnf(c_3711,plain,
    ( k1_relat_1(sK5) = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3586,c_1317])).

cnf(c_37,negated_conjecture,
    ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1588,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))
    | k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_814,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1581,plain,
    ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != X0
    | k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) = k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5)
    | k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) != X0 ),
    inference(instantiation,[status(thm)],[c_814])).

cnf(c_1667,plain,
    ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) = k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5)
    | k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relat_1(sK5)
    | k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) != k2_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1581])).

cnf(c_23,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_41,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_415,plain,
    ( ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_41])).

cnf(c_416,plain,
    ( ~ v1_relat_1(sK5)
    | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5)
    | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_415])).

cnf(c_1316,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5)
    | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5)
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_416])).

cnf(c_44,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_417,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5)
    | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5)
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_416])).

cnf(c_1561,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_1562,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1561])).

cnf(c_1596,plain,
    ( k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5)
    | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1316,c_44,c_417,c_1562])).

cnf(c_1597,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5)
    | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5) ),
    inference(renaming,[status(thm)],[c_1596])).

cnf(c_3702,plain,
    ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) = k2_relat_1(sK5)
    | k1_relat_1(sK5) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3586,c_1597])).

cnf(c_4147,plain,
    ( k1_relat_1(sK5) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3711,c_39,c_37,c_1588,c_1667,c_3702])).

cnf(c_22,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1324,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4165,plain,
    ( sK5 = k1_xboole_0
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4147,c_1324])).

cnf(c_1687,plain,
    ( ~ v1_relat_1(sK5)
    | k1_relat_1(sK5) != k1_xboole_0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_813,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1700,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_813])).

cnf(c_2001,plain,
    ( X0 != X1
    | sK5 != X1
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_814])).

cnf(c_3279,plain,
    ( X0 != sK5
    | sK5 = X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_2001])).

cnf(c_3280,plain,
    ( sK5 != sK5
    | sK5 = k1_xboole_0
    | k1_xboole_0 != sK5 ),
    inference(instantiation,[status(thm)],[c_3279])).

cnf(c_4293,plain,
    ( sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4165,c_39,c_37,c_1561,c_1588,c_1667,c_1687,c_1700,c_3280,c_3702])).

cnf(c_36,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_40,negated_conjecture,
    ( v1_funct_2(sK5,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_552,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_enumset1(sK3,sK3,sK3,sK3) != X1
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X2
    | sK5 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_40])).

cnf(c_553,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))
    | k1_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_enumset1(sK3,sK3,sK3,sK3)
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_552])).

cnf(c_38,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_555,plain,
    ( k1_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_553,c_39,c_38])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k4_tarski(X3,sK1(X0,X3)),X0)
    | k1_relset_1(X1,X2,X0) != X1 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1320,plain,
    ( k1_relset_1(X0,X1,X2) != X0
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r2_hidden(X3,X0) != iProver_top
    | r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3565,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) != iProver_top
    | r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK1(sK5,X0)),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_555,c_1320])).

cnf(c_4168,plain,
    ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK1(sK5,X0)),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3565,c_44])).

cnf(c_4296,plain,
    ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4293,c_4168])).

cnf(c_4836,plain,
    ( r2_hidden(k4_tarski(sK0(X0,X1),sK1(k1_xboole_0,sK0(X0,X1))),k1_xboole_0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3102,c_4296])).

cnf(c_24,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1323,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4976,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top
    | r1_tarski(k1_xboole_0,k4_tarski(sK0(X0,X1),sK1(k1_xboole_0,sK0(X0,X1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4836,c_1323])).

cnf(c_15,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1327,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1672,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1327,c_1315])).

cnf(c_20,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1673,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1672,c_20])).

cnf(c_5453,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4976,c_1673])).

cnf(c_5455,plain,
    ( r1_tarski(k2_enumset1(sK3,sK3,sK3,sK3),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1337,c_5453])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1338,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2957,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_relat_1(sK5)
    | r1_tarski(k2_enumset1(sK3,sK3,sK3,sK3),k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1630,c_1338])).

cnf(c_4151,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_xboole_0
    | r1_tarski(k2_enumset1(sK3,sK3,sK3,sK3),k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4147,c_2957])).

cnf(c_5627,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5455,c_4151])).

cnf(c_4153,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_xboole_0
    | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5) ),
    inference(demodulation,[status(thm)],[c_4147,c_1597])).

cnf(c_19,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_4526,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_xboole_0
    | k2_enumset1(k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4153,c_19,c_4293])).

cnf(c_5838,plain,
    ( k2_enumset1(k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5627,c_4526])).

cnf(c_1321,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2601,plain,
    ( k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1317,c_1321])).

cnf(c_2609,plain,
    ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relat_1(sK5) ),
    inference(demodulation,[status(thm)],[c_2601,c_37])).

cnf(c_4299,plain,
    ( k2_enumset1(k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3)) != k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_4293,c_2609])).

cnf(c_4317,plain,
    ( k2_enumset1(k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3)) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4299,c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5838,c_4317])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:12:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.16/1.04  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.04  
% 2.16/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.16/1.04  
% 2.16/1.04  ------  iProver source info
% 2.16/1.04  
% 2.16/1.04  git: date: 2020-06-30 10:37:57 +0100
% 2.16/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.16/1.04  git: non_committed_changes: false
% 2.16/1.04  git: last_make_outside_of_git: false
% 2.16/1.04  
% 2.16/1.04  ------ 
% 2.16/1.04  
% 2.16/1.04  ------ Input Options
% 2.16/1.04  
% 2.16/1.04  --out_options                           all
% 2.16/1.04  --tptp_safe_out                         true
% 2.16/1.04  --problem_path                          ""
% 2.16/1.04  --include_path                          ""
% 2.16/1.04  --clausifier                            res/vclausify_rel
% 2.16/1.04  --clausifier_options                    --mode clausify
% 2.16/1.04  --stdin                                 false
% 2.16/1.04  --stats_out                             all
% 2.16/1.04  
% 2.16/1.04  ------ General Options
% 2.16/1.04  
% 2.16/1.04  --fof                                   false
% 2.16/1.04  --time_out_real                         305.
% 2.16/1.04  --time_out_virtual                      -1.
% 2.16/1.04  --symbol_type_check                     false
% 2.16/1.04  --clausify_out                          false
% 2.16/1.04  --sig_cnt_out                           false
% 2.16/1.04  --trig_cnt_out                          false
% 2.16/1.04  --trig_cnt_out_tolerance                1.
% 2.16/1.04  --trig_cnt_out_sk_spl                   false
% 2.16/1.04  --abstr_cl_out                          false
% 2.16/1.04  
% 2.16/1.04  ------ Global Options
% 2.16/1.04  
% 2.16/1.04  --schedule                              default
% 2.16/1.04  --add_important_lit                     false
% 2.16/1.04  --prop_solver_per_cl                    1000
% 2.16/1.04  --min_unsat_core                        false
% 2.16/1.04  --soft_assumptions                      false
% 2.16/1.04  --soft_lemma_size                       3
% 2.16/1.04  --prop_impl_unit_size                   0
% 2.16/1.04  --prop_impl_unit                        []
% 2.16/1.04  --share_sel_clauses                     true
% 2.16/1.04  --reset_solvers                         false
% 2.16/1.04  --bc_imp_inh                            [conj_cone]
% 2.16/1.04  --conj_cone_tolerance                   3.
% 2.16/1.04  --extra_neg_conj                        none
% 2.16/1.04  --large_theory_mode                     true
% 2.16/1.04  --prolific_symb_bound                   200
% 2.16/1.04  --lt_threshold                          2000
% 2.16/1.04  --clause_weak_htbl                      true
% 2.16/1.04  --gc_record_bc_elim                     false
% 2.16/1.04  
% 2.16/1.04  ------ Preprocessing Options
% 2.16/1.04  
% 2.16/1.04  --preprocessing_flag                    true
% 2.16/1.04  --time_out_prep_mult                    0.1
% 2.16/1.04  --splitting_mode                        input
% 2.16/1.04  --splitting_grd                         true
% 2.16/1.04  --splitting_cvd                         false
% 2.16/1.04  --splitting_cvd_svl                     false
% 2.16/1.04  --splitting_nvd                         32
% 2.16/1.04  --sub_typing                            true
% 2.16/1.04  --prep_gs_sim                           true
% 2.16/1.04  --prep_unflatten                        true
% 2.16/1.04  --prep_res_sim                          true
% 2.16/1.04  --prep_upred                            true
% 2.16/1.04  --prep_sem_filter                       exhaustive
% 2.16/1.04  --prep_sem_filter_out                   false
% 2.16/1.04  --pred_elim                             true
% 2.16/1.04  --res_sim_input                         true
% 2.16/1.04  --eq_ax_congr_red                       true
% 2.16/1.04  --pure_diseq_elim                       true
% 2.16/1.04  --brand_transform                       false
% 2.16/1.04  --non_eq_to_eq                          false
% 2.16/1.04  --prep_def_merge                        true
% 2.16/1.04  --prep_def_merge_prop_impl              false
% 2.16/1.04  --prep_def_merge_mbd                    true
% 2.16/1.04  --prep_def_merge_tr_red                 false
% 2.16/1.04  --prep_def_merge_tr_cl                  false
% 2.16/1.04  --smt_preprocessing                     true
% 2.16/1.04  --smt_ac_axioms                         fast
% 2.16/1.04  --preprocessed_out                      false
% 2.16/1.04  --preprocessed_stats                    false
% 2.16/1.04  
% 2.16/1.04  ------ Abstraction refinement Options
% 2.16/1.04  
% 2.16/1.04  --abstr_ref                             []
% 2.16/1.04  --abstr_ref_prep                        false
% 2.16/1.04  --abstr_ref_until_sat                   false
% 2.16/1.04  --abstr_ref_sig_restrict                funpre
% 2.16/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 2.16/1.04  --abstr_ref_under                       []
% 2.16/1.04  
% 2.16/1.04  ------ SAT Options
% 2.16/1.04  
% 2.16/1.04  --sat_mode                              false
% 2.16/1.04  --sat_fm_restart_options                ""
% 2.16/1.04  --sat_gr_def                            false
% 2.16/1.04  --sat_epr_types                         true
% 2.16/1.04  --sat_non_cyclic_types                  false
% 2.16/1.04  --sat_finite_models                     false
% 2.16/1.04  --sat_fm_lemmas                         false
% 2.16/1.04  --sat_fm_prep                           false
% 2.16/1.04  --sat_fm_uc_incr                        true
% 2.16/1.04  --sat_out_model                         small
% 2.16/1.04  --sat_out_clauses                       false
% 2.16/1.04  
% 2.16/1.04  ------ QBF Options
% 2.16/1.04  
% 2.16/1.04  --qbf_mode                              false
% 2.16/1.04  --qbf_elim_univ                         false
% 2.16/1.04  --qbf_dom_inst                          none
% 2.16/1.04  --qbf_dom_pre_inst                      false
% 2.16/1.04  --qbf_sk_in                             false
% 2.16/1.04  --qbf_pred_elim                         true
% 2.16/1.04  --qbf_split                             512
% 2.16/1.04  
% 2.16/1.04  ------ BMC1 Options
% 2.16/1.04  
% 2.16/1.04  --bmc1_incremental                      false
% 2.16/1.04  --bmc1_axioms                           reachable_all
% 2.16/1.04  --bmc1_min_bound                        0
% 2.16/1.04  --bmc1_max_bound                        -1
% 2.16/1.04  --bmc1_max_bound_default                -1
% 2.16/1.04  --bmc1_symbol_reachability              true
% 2.16/1.04  --bmc1_property_lemmas                  false
% 2.16/1.04  --bmc1_k_induction                      false
% 2.16/1.04  --bmc1_non_equiv_states                 false
% 2.16/1.04  --bmc1_deadlock                         false
% 2.16/1.04  --bmc1_ucm                              false
% 2.16/1.04  --bmc1_add_unsat_core                   none
% 2.16/1.04  --bmc1_unsat_core_children              false
% 2.16/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 2.16/1.04  --bmc1_out_stat                         full
% 2.16/1.04  --bmc1_ground_init                      false
% 2.16/1.04  --bmc1_pre_inst_next_state              false
% 2.16/1.04  --bmc1_pre_inst_state                   false
% 2.16/1.04  --bmc1_pre_inst_reach_state             false
% 2.16/1.04  --bmc1_out_unsat_core                   false
% 2.16/1.04  --bmc1_aig_witness_out                  false
% 2.16/1.04  --bmc1_verbose                          false
% 2.16/1.04  --bmc1_dump_clauses_tptp                false
% 2.16/1.04  --bmc1_dump_unsat_core_tptp             false
% 2.16/1.04  --bmc1_dump_file                        -
% 2.16/1.04  --bmc1_ucm_expand_uc_limit              128
% 2.16/1.04  --bmc1_ucm_n_expand_iterations          6
% 2.16/1.04  --bmc1_ucm_extend_mode                  1
% 2.16/1.04  --bmc1_ucm_init_mode                    2
% 2.16/1.04  --bmc1_ucm_cone_mode                    none
% 2.16/1.04  --bmc1_ucm_reduced_relation_type        0
% 2.16/1.04  --bmc1_ucm_relax_model                  4
% 2.16/1.04  --bmc1_ucm_full_tr_after_sat            true
% 2.16/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 2.16/1.04  --bmc1_ucm_layered_model                none
% 2.16/1.04  --bmc1_ucm_max_lemma_size               10
% 2.16/1.04  
% 2.16/1.04  ------ AIG Options
% 2.16/1.04  
% 2.16/1.04  --aig_mode                              false
% 2.16/1.04  
% 2.16/1.04  ------ Instantiation Options
% 2.16/1.04  
% 2.16/1.04  --instantiation_flag                    true
% 2.16/1.04  --inst_sos_flag                         false
% 2.16/1.04  --inst_sos_phase                        true
% 2.16/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.16/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.16/1.04  --inst_lit_sel_side                     num_symb
% 2.16/1.04  --inst_solver_per_active                1400
% 2.16/1.04  --inst_solver_calls_frac                1.
% 2.16/1.04  --inst_passive_queue_type               priority_queues
% 2.16/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.16/1.04  --inst_passive_queues_freq              [25;2]
% 2.16/1.04  --inst_dismatching                      true
% 2.16/1.04  --inst_eager_unprocessed_to_passive     true
% 2.16/1.04  --inst_prop_sim_given                   true
% 2.16/1.04  --inst_prop_sim_new                     false
% 2.16/1.04  --inst_subs_new                         false
% 2.16/1.04  --inst_eq_res_simp                      false
% 2.16/1.04  --inst_subs_given                       false
% 2.16/1.04  --inst_orphan_elimination               true
% 2.16/1.04  --inst_learning_loop_flag               true
% 2.16/1.04  --inst_learning_start                   3000
% 2.16/1.04  --inst_learning_factor                  2
% 2.16/1.04  --inst_start_prop_sim_after_learn       3
% 2.16/1.04  --inst_sel_renew                        solver
% 2.16/1.04  --inst_lit_activity_flag                true
% 2.16/1.04  --inst_restr_to_given                   false
% 2.16/1.04  --inst_activity_threshold               500
% 2.16/1.04  --inst_out_proof                        true
% 2.16/1.04  
% 2.16/1.04  ------ Resolution Options
% 2.16/1.04  
% 2.16/1.04  --resolution_flag                       true
% 2.16/1.04  --res_lit_sel                           adaptive
% 2.16/1.04  --res_lit_sel_side                      none
% 2.16/1.04  --res_ordering                          kbo
% 2.16/1.04  --res_to_prop_solver                    active
% 2.16/1.04  --res_prop_simpl_new                    false
% 2.16/1.04  --res_prop_simpl_given                  true
% 2.16/1.04  --res_passive_queue_type                priority_queues
% 2.16/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.16/1.04  --res_passive_queues_freq               [15;5]
% 2.16/1.04  --res_forward_subs                      full
% 2.16/1.04  --res_backward_subs                     full
% 2.16/1.04  --res_forward_subs_resolution           true
% 2.16/1.04  --res_backward_subs_resolution          true
% 2.16/1.04  --res_orphan_elimination                true
% 2.16/1.04  --res_time_limit                        2.
% 2.16/1.04  --res_out_proof                         true
% 2.16/1.04  
% 2.16/1.04  ------ Superposition Options
% 2.16/1.04  
% 2.16/1.04  --superposition_flag                    true
% 2.16/1.04  --sup_passive_queue_type                priority_queues
% 2.16/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.16/1.04  --sup_passive_queues_freq               [8;1;4]
% 2.16/1.04  --demod_completeness_check              fast
% 2.16/1.04  --demod_use_ground                      true
% 2.16/1.04  --sup_to_prop_solver                    passive
% 2.16/1.04  --sup_prop_simpl_new                    true
% 2.16/1.04  --sup_prop_simpl_given                  true
% 2.16/1.04  --sup_fun_splitting                     false
% 2.16/1.04  --sup_smt_interval                      50000
% 2.16/1.04  
% 2.16/1.04  ------ Superposition Simplification Setup
% 2.16/1.04  
% 2.16/1.04  --sup_indices_passive                   []
% 2.16/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 2.16/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.04  --sup_full_bw                           [BwDemod]
% 2.16/1.04  --sup_immed_triv                        [TrivRules]
% 2.16/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.16/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.04  --sup_immed_bw_main                     []
% 2.16/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.16/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 2.16/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.16/1.04  
% 2.16/1.04  ------ Combination Options
% 2.16/1.04  
% 2.16/1.04  --comb_res_mult                         3
% 2.16/1.04  --comb_sup_mult                         2
% 2.16/1.04  --comb_inst_mult                        10
% 2.16/1.04  
% 2.16/1.04  ------ Debug Options
% 2.16/1.04  
% 2.16/1.04  --dbg_backtrace                         false
% 2.16/1.04  --dbg_dump_prop_clauses                 false
% 2.16/1.04  --dbg_dump_prop_clauses_file            -
% 2.16/1.04  --dbg_out_stat                          false
% 2.16/1.04  ------ Parsing...
% 2.16/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.16/1.04  
% 2.16/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.16/1.04  
% 2.16/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.16/1.04  
% 2.16/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.16/1.04  ------ Proving...
% 2.16/1.04  ------ Problem Properties 
% 2.16/1.04  
% 2.16/1.04  
% 2.16/1.04  clauses                                 34
% 2.16/1.04  conjectures                             3
% 2.16/1.04  EPR                                     5
% 2.16/1.04  Horn                                    30
% 2.16/1.04  unary                                   16
% 2.16/1.04  binary                                  6
% 2.16/1.04  lits                                    72
% 2.16/1.04  lits eq                                 29
% 2.16/1.04  fd_pure                                 0
% 2.16/1.04  fd_pseudo                               0
% 2.16/1.04  fd_cond                                 2
% 2.16/1.04  fd_pseudo_cond                          2
% 2.16/1.04  AC symbols                              0
% 2.16/1.04  
% 2.16/1.04  ------ Schedule dynamic 5 is on 
% 2.16/1.04  
% 2.16/1.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.16/1.04  
% 2.16/1.04  
% 2.16/1.04  ------ 
% 2.16/1.04  Current options:
% 2.16/1.04  ------ 
% 2.16/1.04  
% 2.16/1.04  ------ Input Options
% 2.16/1.04  
% 2.16/1.04  --out_options                           all
% 2.16/1.04  --tptp_safe_out                         true
% 2.16/1.04  --problem_path                          ""
% 2.16/1.04  --include_path                          ""
% 2.16/1.04  --clausifier                            res/vclausify_rel
% 2.16/1.04  --clausifier_options                    --mode clausify
% 2.16/1.04  --stdin                                 false
% 2.16/1.04  --stats_out                             all
% 2.16/1.04  
% 2.16/1.04  ------ General Options
% 2.16/1.04  
% 2.16/1.04  --fof                                   false
% 2.16/1.04  --time_out_real                         305.
% 2.16/1.04  --time_out_virtual                      -1.
% 2.16/1.04  --symbol_type_check                     false
% 2.16/1.04  --clausify_out                          false
% 2.16/1.04  --sig_cnt_out                           false
% 2.16/1.04  --trig_cnt_out                          false
% 2.16/1.04  --trig_cnt_out_tolerance                1.
% 2.16/1.04  --trig_cnt_out_sk_spl                   false
% 2.16/1.04  --abstr_cl_out                          false
% 2.16/1.04  
% 2.16/1.04  ------ Global Options
% 2.16/1.04  
% 2.16/1.04  --schedule                              default
% 2.16/1.04  --add_important_lit                     false
% 2.16/1.04  --prop_solver_per_cl                    1000
% 2.16/1.04  --min_unsat_core                        false
% 2.16/1.04  --soft_assumptions                      false
% 2.16/1.04  --soft_lemma_size                       3
% 2.16/1.04  --prop_impl_unit_size                   0
% 2.16/1.04  --prop_impl_unit                        []
% 2.16/1.04  --share_sel_clauses                     true
% 2.16/1.04  --reset_solvers                         false
% 2.16/1.04  --bc_imp_inh                            [conj_cone]
% 2.16/1.04  --conj_cone_tolerance                   3.
% 2.16/1.04  --extra_neg_conj                        none
% 2.16/1.04  --large_theory_mode                     true
% 2.16/1.04  --prolific_symb_bound                   200
% 2.16/1.04  --lt_threshold                          2000
% 2.16/1.04  --clause_weak_htbl                      true
% 2.16/1.04  --gc_record_bc_elim                     false
% 2.16/1.04  
% 2.16/1.04  ------ Preprocessing Options
% 2.16/1.04  
% 2.16/1.04  --preprocessing_flag                    true
% 2.16/1.04  --time_out_prep_mult                    0.1
% 2.16/1.04  --splitting_mode                        input
% 2.16/1.04  --splitting_grd                         true
% 2.16/1.04  --splitting_cvd                         false
% 2.16/1.04  --splitting_cvd_svl                     false
% 2.16/1.04  --splitting_nvd                         32
% 2.16/1.04  --sub_typing                            true
% 2.16/1.04  --prep_gs_sim                           true
% 2.16/1.04  --prep_unflatten                        true
% 2.16/1.04  --prep_res_sim                          true
% 2.16/1.04  --prep_upred                            true
% 2.16/1.04  --prep_sem_filter                       exhaustive
% 2.16/1.04  --prep_sem_filter_out                   false
% 2.16/1.04  --pred_elim                             true
% 2.16/1.04  --res_sim_input                         true
% 2.16/1.04  --eq_ax_congr_red                       true
% 2.16/1.04  --pure_diseq_elim                       true
% 2.16/1.04  --brand_transform                       false
% 2.16/1.04  --non_eq_to_eq                          false
% 2.16/1.04  --prep_def_merge                        true
% 2.16/1.04  --prep_def_merge_prop_impl              false
% 2.16/1.04  --prep_def_merge_mbd                    true
% 2.16/1.04  --prep_def_merge_tr_red                 false
% 2.16/1.04  --prep_def_merge_tr_cl                  false
% 2.16/1.04  --smt_preprocessing                     true
% 2.16/1.04  --smt_ac_axioms                         fast
% 2.16/1.04  --preprocessed_out                      false
% 2.16/1.04  --preprocessed_stats                    false
% 2.16/1.04  
% 2.16/1.04  ------ Abstraction refinement Options
% 2.16/1.04  
% 2.16/1.04  --abstr_ref                             []
% 2.16/1.04  --abstr_ref_prep                        false
% 2.16/1.04  --abstr_ref_until_sat                   false
% 2.16/1.04  --abstr_ref_sig_restrict                funpre
% 2.16/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 2.16/1.04  --abstr_ref_under                       []
% 2.16/1.04  
% 2.16/1.04  ------ SAT Options
% 2.16/1.04  
% 2.16/1.04  --sat_mode                              false
% 2.16/1.04  --sat_fm_restart_options                ""
% 2.16/1.04  --sat_gr_def                            false
% 2.16/1.04  --sat_epr_types                         true
% 2.16/1.04  --sat_non_cyclic_types                  false
% 2.16/1.04  --sat_finite_models                     false
% 2.16/1.04  --sat_fm_lemmas                         false
% 2.16/1.04  --sat_fm_prep                           false
% 2.16/1.04  --sat_fm_uc_incr                        true
% 2.16/1.04  --sat_out_model                         small
% 2.16/1.04  --sat_out_clauses                       false
% 2.16/1.04  
% 2.16/1.04  ------ QBF Options
% 2.16/1.04  
% 2.16/1.04  --qbf_mode                              false
% 2.16/1.04  --qbf_elim_univ                         false
% 2.16/1.04  --qbf_dom_inst                          none
% 2.16/1.04  --qbf_dom_pre_inst                      false
% 2.16/1.04  --qbf_sk_in                             false
% 2.16/1.04  --qbf_pred_elim                         true
% 2.16/1.04  --qbf_split                             512
% 2.16/1.04  
% 2.16/1.04  ------ BMC1 Options
% 2.16/1.04  
% 2.16/1.04  --bmc1_incremental                      false
% 2.16/1.04  --bmc1_axioms                           reachable_all
% 2.16/1.04  --bmc1_min_bound                        0
% 2.16/1.04  --bmc1_max_bound                        -1
% 2.16/1.04  --bmc1_max_bound_default                -1
% 2.16/1.04  --bmc1_symbol_reachability              true
% 2.16/1.04  --bmc1_property_lemmas                  false
% 2.16/1.04  --bmc1_k_induction                      false
% 2.16/1.04  --bmc1_non_equiv_states                 false
% 2.16/1.04  --bmc1_deadlock                         false
% 2.16/1.04  --bmc1_ucm                              false
% 2.16/1.04  --bmc1_add_unsat_core                   none
% 2.16/1.04  --bmc1_unsat_core_children              false
% 2.16/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 2.16/1.04  --bmc1_out_stat                         full
% 2.16/1.04  --bmc1_ground_init                      false
% 2.16/1.04  --bmc1_pre_inst_next_state              false
% 2.16/1.04  --bmc1_pre_inst_state                   false
% 2.16/1.04  --bmc1_pre_inst_reach_state             false
% 2.16/1.04  --bmc1_out_unsat_core                   false
% 2.16/1.04  --bmc1_aig_witness_out                  false
% 2.16/1.04  --bmc1_verbose                          false
% 2.16/1.04  --bmc1_dump_clauses_tptp                false
% 2.16/1.04  --bmc1_dump_unsat_core_tptp             false
% 2.16/1.04  --bmc1_dump_file                        -
% 2.16/1.04  --bmc1_ucm_expand_uc_limit              128
% 2.16/1.04  --bmc1_ucm_n_expand_iterations          6
% 2.16/1.04  --bmc1_ucm_extend_mode                  1
% 2.16/1.04  --bmc1_ucm_init_mode                    2
% 2.16/1.04  --bmc1_ucm_cone_mode                    none
% 2.16/1.04  --bmc1_ucm_reduced_relation_type        0
% 2.16/1.04  --bmc1_ucm_relax_model                  4
% 2.16/1.04  --bmc1_ucm_full_tr_after_sat            true
% 2.16/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 2.16/1.04  --bmc1_ucm_layered_model                none
% 2.16/1.04  --bmc1_ucm_max_lemma_size               10
% 2.16/1.04  
% 2.16/1.04  ------ AIG Options
% 2.16/1.04  
% 2.16/1.04  --aig_mode                              false
% 2.16/1.04  
% 2.16/1.04  ------ Instantiation Options
% 2.16/1.04  
% 2.16/1.04  --instantiation_flag                    true
% 2.16/1.04  --inst_sos_flag                         false
% 2.16/1.04  --inst_sos_phase                        true
% 2.16/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.16/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.16/1.04  --inst_lit_sel_side                     none
% 2.16/1.04  --inst_solver_per_active                1400
% 2.16/1.04  --inst_solver_calls_frac                1.
% 2.16/1.04  --inst_passive_queue_type               priority_queues
% 2.16/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.16/1.04  --inst_passive_queues_freq              [25;2]
% 2.16/1.04  --inst_dismatching                      true
% 2.16/1.04  --inst_eager_unprocessed_to_passive     true
% 2.16/1.04  --inst_prop_sim_given                   true
% 2.16/1.04  --inst_prop_sim_new                     false
% 2.16/1.04  --inst_subs_new                         false
% 2.16/1.04  --inst_eq_res_simp                      false
% 2.16/1.04  --inst_subs_given                       false
% 2.16/1.04  --inst_orphan_elimination               true
% 2.16/1.04  --inst_learning_loop_flag               true
% 2.16/1.04  --inst_learning_start                   3000
% 2.16/1.04  --inst_learning_factor                  2
% 2.16/1.04  --inst_start_prop_sim_after_learn       3
% 2.16/1.04  --inst_sel_renew                        solver
% 2.16/1.04  --inst_lit_activity_flag                true
% 2.16/1.04  --inst_restr_to_given                   false
% 2.16/1.04  --inst_activity_threshold               500
% 2.16/1.04  --inst_out_proof                        true
% 2.16/1.04  
% 2.16/1.04  ------ Resolution Options
% 2.16/1.04  
% 2.16/1.04  --resolution_flag                       false
% 2.16/1.04  --res_lit_sel                           adaptive
% 2.16/1.04  --res_lit_sel_side                      none
% 2.16/1.04  --res_ordering                          kbo
% 2.16/1.05  --res_to_prop_solver                    active
% 2.16/1.05  --res_prop_simpl_new                    false
% 2.16/1.05  --res_prop_simpl_given                  true
% 2.16/1.05  --res_passive_queue_type                priority_queues
% 2.16/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.16/1.05  --res_passive_queues_freq               [15;5]
% 2.16/1.05  --res_forward_subs                      full
% 2.16/1.05  --res_backward_subs                     full
% 2.16/1.05  --res_forward_subs_resolution           true
% 2.16/1.05  --res_backward_subs_resolution          true
% 2.16/1.05  --res_orphan_elimination                true
% 2.16/1.05  --res_time_limit                        2.
% 2.16/1.05  --res_out_proof                         true
% 2.16/1.05  
% 2.16/1.05  ------ Superposition Options
% 2.16/1.05  
% 2.16/1.05  --superposition_flag                    true
% 2.16/1.05  --sup_passive_queue_type                priority_queues
% 2.16/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.16/1.05  --sup_passive_queues_freq               [8;1;4]
% 2.16/1.05  --demod_completeness_check              fast
% 2.16/1.05  --demod_use_ground                      true
% 2.16/1.05  --sup_to_prop_solver                    passive
% 2.16/1.05  --sup_prop_simpl_new                    true
% 2.16/1.05  --sup_prop_simpl_given                  true
% 2.16/1.05  --sup_fun_splitting                     false
% 2.16/1.05  --sup_smt_interval                      50000
% 2.16/1.05  
% 2.16/1.05  ------ Superposition Simplification Setup
% 2.16/1.05  
% 2.16/1.05  --sup_indices_passive                   []
% 2.16/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 2.16/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.05  --sup_full_bw                           [BwDemod]
% 2.16/1.05  --sup_immed_triv                        [TrivRules]
% 2.16/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.16/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.05  --sup_immed_bw_main                     []
% 2.16/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.16/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 2.16/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.16/1.05  
% 2.16/1.05  ------ Combination Options
% 2.16/1.05  
% 2.16/1.05  --comb_res_mult                         3
% 2.16/1.05  --comb_sup_mult                         2
% 2.16/1.05  --comb_inst_mult                        10
% 2.16/1.05  
% 2.16/1.05  ------ Debug Options
% 2.16/1.05  
% 2.16/1.05  --dbg_backtrace                         false
% 2.16/1.05  --dbg_dump_prop_clauses                 false
% 2.16/1.05  --dbg_dump_prop_clauses_file            -
% 2.16/1.05  --dbg_out_stat                          false
% 2.16/1.05  
% 2.16/1.05  
% 2.16/1.05  
% 2.16/1.05  
% 2.16/1.05  ------ Proving...
% 2.16/1.05  
% 2.16/1.05  
% 2.16/1.05  % SZS status Theorem for theBenchmark.p
% 2.16/1.05  
% 2.16/1.05  % SZS output start CNFRefutation for theBenchmark.p
% 2.16/1.05  
% 2.16/1.05  fof(f2,axiom,(
% 2.16/1.05    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.16/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.05  
% 2.16/1.05  fof(f44,plain,(
% 2.16/1.05    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.16/1.05    inference(nnf_transformation,[],[f2])).
% 2.16/1.05  
% 2.16/1.05  fof(f45,plain,(
% 2.16/1.05    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.16/1.05    inference(flattening,[],[f44])).
% 2.16/1.05  
% 2.16/1.05  fof(f61,plain,(
% 2.16/1.05    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.16/1.05    inference(cnf_transformation,[],[f45])).
% 2.16/1.05  
% 2.16/1.05  fof(f117,plain,(
% 2.16/1.05    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.16/1.05    inference(equality_resolution,[],[f61])).
% 2.16/1.05  
% 2.16/1.05  fof(f1,axiom,(
% 2.16/1.05    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.16/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.05  
% 2.16/1.05  fof(f22,plain,(
% 2.16/1.05    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.16/1.05    inference(ennf_transformation,[],[f1])).
% 2.16/1.05  
% 2.16/1.05  fof(f40,plain,(
% 2.16/1.05    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.16/1.05    inference(nnf_transformation,[],[f22])).
% 2.16/1.05  
% 2.16/1.05  fof(f41,plain,(
% 2.16/1.05    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.16/1.05    inference(rectify,[],[f40])).
% 2.16/1.05  
% 2.16/1.05  fof(f42,plain,(
% 2.16/1.05    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.16/1.05    introduced(choice_axiom,[])).
% 2.16/1.05  
% 2.16/1.05  fof(f43,plain,(
% 2.16/1.05    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.16/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f42])).
% 2.16/1.05  
% 2.16/1.05  fof(f58,plain,(
% 2.16/1.05    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.16/1.05    inference(cnf_transformation,[],[f43])).
% 2.16/1.05  
% 2.16/1.05  fof(f57,plain,(
% 2.16/1.05    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.16/1.05    inference(cnf_transformation,[],[f43])).
% 2.16/1.05  
% 2.16/1.05  fof(f19,conjecture,(
% 2.16/1.05    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 2.16/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.05  
% 2.16/1.05  fof(f20,negated_conjecture,(
% 2.16/1.05    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 2.16/1.05    inference(negated_conjecture,[],[f19])).
% 2.16/1.05  
% 2.16/1.05  fof(f38,plain,(
% 2.16/1.05    ? [X0,X1,X2] : ((k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 2.16/1.05    inference(ennf_transformation,[],[f20])).
% 2.16/1.05  
% 2.16/1.05  fof(f39,plain,(
% 2.16/1.05    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 2.16/1.05    inference(flattening,[],[f38])).
% 2.16/1.05  
% 2.16/1.05  fof(f55,plain,(
% 2.16/1.05    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_tarski(k1_funct_1(sK5,sK3)) != k2_relset_1(k1_tarski(sK3),sK4,sK5) & k1_xboole_0 != sK4 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4))) & v1_funct_2(sK5,k1_tarski(sK3),sK4) & v1_funct_1(sK5))),
% 2.16/1.05    introduced(choice_axiom,[])).
% 2.16/1.05  
% 2.16/1.05  fof(f56,plain,(
% 2.16/1.05    k1_tarski(k1_funct_1(sK5,sK3)) != k2_relset_1(k1_tarski(sK3),sK4,sK5) & k1_xboole_0 != sK4 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4))) & v1_funct_2(sK5,k1_tarski(sK3),sK4) & v1_funct_1(sK5)),
% 2.16/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f39,f55])).
% 2.16/1.05  
% 2.16/1.05  fof(f99,plain,(
% 2.16/1.05    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4)))),
% 2.16/1.05    inference(cnf_transformation,[],[f56])).
% 2.16/1.05  
% 2.16/1.05  fof(f3,axiom,(
% 2.16/1.05    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.16/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.05  
% 2.16/1.05  fof(f63,plain,(
% 2.16/1.05    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.16/1.05    inference(cnf_transformation,[],[f3])).
% 2.16/1.05  
% 2.16/1.05  fof(f4,axiom,(
% 2.16/1.05    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.16/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.05  
% 2.16/1.05  fof(f64,plain,(
% 2.16/1.05    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.16/1.05    inference(cnf_transformation,[],[f4])).
% 2.16/1.05  
% 2.16/1.05  fof(f5,axiom,(
% 2.16/1.05    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.16/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.05  
% 2.16/1.05  fof(f65,plain,(
% 2.16/1.05    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.16/1.05    inference(cnf_transformation,[],[f5])).
% 2.16/1.05  
% 2.16/1.05  fof(f102,plain,(
% 2.16/1.05    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.16/1.05    inference(definition_unfolding,[],[f64,f65])).
% 2.16/1.05  
% 2.16/1.05  fof(f103,plain,(
% 2.16/1.05    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.16/1.05    inference(definition_unfolding,[],[f63,f102])).
% 2.16/1.05  
% 2.16/1.05  fof(f115,plain,(
% 2.16/1.05    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))),
% 2.16/1.05    inference(definition_unfolding,[],[f99,f103])).
% 2.16/1.05  
% 2.16/1.05  fof(f15,axiom,(
% 2.16/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.16/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.05  
% 2.16/1.05  fof(f21,plain,(
% 2.16/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.16/1.05    inference(pure_predicate_removal,[],[f15])).
% 2.16/1.05  
% 2.16/1.05  fof(f33,plain,(
% 2.16/1.05    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.16/1.05    inference(ennf_transformation,[],[f21])).
% 2.16/1.05  
% 2.16/1.05  fof(f86,plain,(
% 2.16/1.05    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.16/1.05    inference(cnf_transformation,[],[f33])).
% 2.16/1.05  
% 2.16/1.05  fof(f9,axiom,(
% 2.16/1.05    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.16/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.05  
% 2.16/1.05  fof(f26,plain,(
% 2.16/1.05    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.16/1.05    inference(ennf_transformation,[],[f9])).
% 2.16/1.05  
% 2.16/1.05  fof(f48,plain,(
% 2.16/1.05    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.16/1.05    inference(nnf_transformation,[],[f26])).
% 2.16/1.05  
% 2.16/1.05  fof(f77,plain,(
% 2.16/1.05    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.16/1.05    inference(cnf_transformation,[],[f48])).
% 2.16/1.05  
% 2.16/1.05  fof(f14,axiom,(
% 2.16/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.16/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.05  
% 2.16/1.05  fof(f32,plain,(
% 2.16/1.05    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.16/1.05    inference(ennf_transformation,[],[f14])).
% 2.16/1.05  
% 2.16/1.05  fof(f85,plain,(
% 2.16/1.05    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.16/1.05    inference(cnf_transformation,[],[f32])).
% 2.16/1.05  
% 2.16/1.05  fof(f6,axiom,(
% 2.16/1.05    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> ~(k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3))),
% 2.16/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.05  
% 2.16/1.05  fof(f23,plain,(
% 2.16/1.05    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3))),
% 2.16/1.05    inference(ennf_transformation,[],[f6])).
% 2.16/1.05  
% 2.16/1.05  fof(f46,plain,(
% 2.16/1.05    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & ((k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3) | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 2.16/1.05    inference(nnf_transformation,[],[f23])).
% 2.16/1.05  
% 2.16/1.05  fof(f47,plain,(
% 2.16/1.05    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 2.16/1.05    inference(flattening,[],[f46])).
% 2.16/1.05  
% 2.16/1.05  fof(f66,plain,(
% 2.16/1.05    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))) )),
% 2.16/1.05    inference(cnf_transformation,[],[f47])).
% 2.16/1.05  
% 2.16/1.05  fof(f112,plain,(
% 2.16/1.05    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X0,X1,X2) = X3 | k2_enumset1(X0,X0,X0,X2) = X3 | k2_enumset1(X1,X1,X1,X2) = X3 | k2_enumset1(X0,X0,X0,X1) = X3 | k2_enumset1(X2,X2,X2,X2) = X3 | k2_enumset1(X1,X1,X1,X1) = X3 | k2_enumset1(X0,X0,X0,X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k2_enumset1(X0,X0,X1,X2))) )),
% 2.16/1.05    inference(definition_unfolding,[],[f66,f65,f102,f102,f102,f103,f103,f103,f65])).
% 2.16/1.05  
% 2.16/1.05  fof(f101,plain,(
% 2.16/1.05    k1_tarski(k1_funct_1(sK5,sK3)) != k2_relset_1(k1_tarski(sK3),sK4,sK5)),
% 2.16/1.05    inference(cnf_transformation,[],[f56])).
% 2.16/1.05  
% 2.16/1.05  fof(f114,plain,(
% 2.16/1.05    k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5)),
% 2.16/1.05    inference(definition_unfolding,[],[f101,f103,f103])).
% 2.16/1.05  
% 2.16/1.05  fof(f16,axiom,(
% 2.16/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.16/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.05  
% 2.16/1.05  fof(f34,plain,(
% 2.16/1.05    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.16/1.05    inference(ennf_transformation,[],[f16])).
% 2.16/1.05  
% 2.16/1.05  fof(f87,plain,(
% 2.16/1.05    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.16/1.05    inference(cnf_transformation,[],[f34])).
% 2.16/1.05  
% 2.16/1.05  fof(f12,axiom,(
% 2.16/1.05    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 2.16/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.05  
% 2.16/1.05  fof(f29,plain,(
% 2.16/1.05    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.16/1.05    inference(ennf_transformation,[],[f12])).
% 2.16/1.05  
% 2.16/1.05  fof(f30,plain,(
% 2.16/1.05    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.16/1.05    inference(flattening,[],[f29])).
% 2.16/1.05  
% 2.16/1.05  fof(f83,plain,(
% 2.16/1.05    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.16/1.05    inference(cnf_transformation,[],[f30])).
% 2.16/1.05  
% 2.16/1.05  fof(f113,plain,(
% 2.16/1.05    ( ! [X0,X1] : (k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1) | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.16/1.05    inference(definition_unfolding,[],[f83,f103,f103])).
% 2.16/1.05  
% 2.16/1.05  fof(f97,plain,(
% 2.16/1.05    v1_funct_1(sK5)),
% 2.16/1.05    inference(cnf_transformation,[],[f56])).
% 2.16/1.05  
% 2.16/1.05  fof(f11,axiom,(
% 2.16/1.05    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 2.16/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.05  
% 2.16/1.05  fof(f27,plain,(
% 2.16/1.05    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.16/1.05    inference(ennf_transformation,[],[f11])).
% 2.16/1.05  
% 2.16/1.05  fof(f28,plain,(
% 2.16/1.05    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.16/1.05    inference(flattening,[],[f27])).
% 2.16/1.05  
% 2.16/1.05  fof(f81,plain,(
% 2.16/1.05    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.16/1.05    inference(cnf_transformation,[],[f28])).
% 2.16/1.05  
% 2.16/1.05  fof(f18,axiom,(
% 2.16/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.16/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.05  
% 2.16/1.05  fof(f36,plain,(
% 2.16/1.05    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.16/1.05    inference(ennf_transformation,[],[f18])).
% 2.16/1.05  
% 2.16/1.05  fof(f37,plain,(
% 2.16/1.05    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.16/1.05    inference(flattening,[],[f36])).
% 2.16/1.05  
% 2.16/1.05  fof(f54,plain,(
% 2.16/1.05    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.16/1.05    inference(nnf_transformation,[],[f37])).
% 2.16/1.05  
% 2.16/1.05  fof(f91,plain,(
% 2.16/1.05    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.16/1.05    inference(cnf_transformation,[],[f54])).
% 2.16/1.05  
% 2.16/1.05  fof(f98,plain,(
% 2.16/1.05    v1_funct_2(sK5,k1_tarski(sK3),sK4)),
% 2.16/1.05    inference(cnf_transformation,[],[f56])).
% 2.16/1.05  
% 2.16/1.05  fof(f116,plain,(
% 2.16/1.05    v1_funct_2(sK5,k2_enumset1(sK3,sK3,sK3,sK3),sK4)),
% 2.16/1.05    inference(definition_unfolding,[],[f98,f103])).
% 2.16/1.05  
% 2.16/1.05  fof(f100,plain,(
% 2.16/1.05    k1_xboole_0 != sK4),
% 2.16/1.05    inference(cnf_transformation,[],[f56])).
% 2.16/1.05  
% 2.16/1.05  fof(f17,axiom,(
% 2.16/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 2.16/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.05  
% 2.16/1.05  fof(f35,plain,(
% 2.16/1.05    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.16/1.05    inference(ennf_transformation,[],[f17])).
% 2.16/1.05  
% 2.16/1.05  fof(f49,plain,(
% 2.16/1.05    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.16/1.05    inference(nnf_transformation,[],[f35])).
% 2.16/1.05  
% 2.16/1.05  fof(f50,plain,(
% 2.16/1.05    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.16/1.05    inference(rectify,[],[f49])).
% 2.16/1.05  
% 2.16/1.05  fof(f52,plain,(
% 2.16/1.05    ! [X2,X1] : (? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)) => (! [X6] : ~r2_hidden(k4_tarski(sK2(X1,X2),X6),X2) & r2_hidden(sK2(X1,X2),X1)))),
% 2.16/1.05    introduced(choice_axiom,[])).
% 2.16/1.05  
% 2.16/1.05  fof(f51,plain,(
% 2.16/1.05    ! [X3,X2] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) => r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2))),
% 2.16/1.05    introduced(choice_axiom,[])).
% 2.16/1.05  
% 2.16/1.05  fof(f53,plain,(
% 2.16/1.05    ! [X0,X1,X2] : (((! [X3] : (r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | (! [X6] : ~r2_hidden(k4_tarski(sK2(X1,X2),X6),X2) & r2_hidden(sK2(X1,X2),X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.16/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f50,f52,f51])).
% 2.16/1.05  
% 2.16/1.05  fof(f90,plain,(
% 2.16/1.05    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2) | ~r2_hidden(X3,X1) | k1_relset_1(X1,X0,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 2.16/1.05    inference(cnf_transformation,[],[f53])).
% 2.16/1.05  
% 2.16/1.05  fof(f13,axiom,(
% 2.16/1.05    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.16/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.05  
% 2.16/1.05  fof(f31,plain,(
% 2.16/1.05    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.16/1.05    inference(ennf_transformation,[],[f13])).
% 2.16/1.05  
% 2.16/1.05  fof(f84,plain,(
% 2.16/1.05    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.16/1.05    inference(cnf_transformation,[],[f31])).
% 2.16/1.05  
% 2.16/1.05  fof(f7,axiom,(
% 2.16/1.05    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.16/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.05  
% 2.16/1.05  fof(f75,plain,(
% 2.16/1.05    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.16/1.05    inference(cnf_transformation,[],[f7])).
% 2.16/1.05  
% 2.16/1.05  fof(f10,axiom,(
% 2.16/1.05    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.16/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.05  
% 2.16/1.05  fof(f79,plain,(
% 2.16/1.05    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.16/1.05    inference(cnf_transformation,[],[f10])).
% 2.16/1.05  
% 2.16/1.05  fof(f62,plain,(
% 2.16/1.05    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.16/1.05    inference(cnf_transformation,[],[f45])).
% 2.16/1.05  
% 2.16/1.05  fof(f80,plain,(
% 2.16/1.05    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 2.16/1.05    inference(cnf_transformation,[],[f10])).
% 2.16/1.05  
% 2.16/1.05  cnf(c_4,plain,
% 2.16/1.05      ( r1_tarski(X0,X0) ),
% 2.16/1.05      inference(cnf_transformation,[],[f117]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1337,plain,
% 2.16/1.05      ( r1_tarski(X0,X0) = iProver_top ),
% 2.16/1.05      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1,plain,
% 2.16/1.05      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.16/1.05      inference(cnf_transformation,[],[f58]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1340,plain,
% 2.16/1.05      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 2.16/1.05      | r1_tarski(X0,X1) = iProver_top ),
% 2.16/1.05      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_2,plain,
% 2.16/1.05      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 2.16/1.05      inference(cnf_transformation,[],[f57]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1339,plain,
% 2.16/1.05      ( r2_hidden(X0,X1) != iProver_top
% 2.16/1.05      | r2_hidden(X0,X2) = iProver_top
% 2.16/1.05      | r1_tarski(X1,X2) != iProver_top ),
% 2.16/1.05      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_3102,plain,
% 2.16/1.05      ( r2_hidden(sK0(X0,X1),X2) = iProver_top
% 2.16/1.05      | r1_tarski(X0,X2) != iProver_top
% 2.16/1.05      | r1_tarski(X0,X1) = iProver_top ),
% 2.16/1.05      inference(superposition,[status(thm)],[c_1340,c_1339]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_39,negated_conjecture,
% 2.16/1.05      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) ),
% 2.16/1.05      inference(cnf_transformation,[],[f115]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1317,plain,
% 2.16/1.05      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) = iProver_top ),
% 2.16/1.05      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_26,plain,
% 2.16/1.05      ( v4_relat_1(X0,X1)
% 2.16/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.16/1.05      inference(cnf_transformation,[],[f86]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_18,plain,
% 2.16/1.05      ( ~ v4_relat_1(X0,X1)
% 2.16/1.05      | r1_tarski(k1_relat_1(X0),X1)
% 2.16/1.05      | ~ v1_relat_1(X0) ),
% 2.16/1.05      inference(cnf_transformation,[],[f77]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_434,plain,
% 2.16/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.16/1.05      | r1_tarski(k1_relat_1(X0),X1)
% 2.16/1.05      | ~ v1_relat_1(X0) ),
% 2.16/1.05      inference(resolution,[status(thm)],[c_26,c_18]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_25,plain,
% 2.16/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.16/1.05      | v1_relat_1(X0) ),
% 2.16/1.05      inference(cnf_transformation,[],[f85]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_438,plain,
% 2.16/1.05      ( r1_tarski(k1_relat_1(X0),X1)
% 2.16/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.16/1.05      inference(global_propositional_subsumption,
% 2.16/1.05                [status(thm)],
% 2.16/1.05                [c_434,c_25]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_439,plain,
% 2.16/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.16/1.05      | r1_tarski(k1_relat_1(X0),X1) ),
% 2.16/1.05      inference(renaming,[status(thm)],[c_438]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1315,plain,
% 2.16/1.05      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.16/1.05      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 2.16/1.05      inference(predicate_to_equality,[status(thm)],[c_439]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1630,plain,
% 2.16/1.05      ( r1_tarski(k1_relat_1(sK5),k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top ),
% 2.16/1.05      inference(superposition,[status(thm)],[c_1317,c_1315]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_14,plain,
% 2.16/1.05      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X2,X3))
% 2.16/1.05      | k2_enumset1(X1,X1,X2,X3) = X0
% 2.16/1.05      | k2_enumset1(X1,X1,X1,X3) = X0
% 2.16/1.05      | k2_enumset1(X2,X2,X2,X3) = X0
% 2.16/1.05      | k2_enumset1(X1,X1,X1,X2) = X0
% 2.16/1.05      | k2_enumset1(X3,X3,X3,X3) = X0
% 2.16/1.05      | k2_enumset1(X2,X2,X2,X2) = X0
% 2.16/1.05      | k2_enumset1(X1,X1,X1,X1) = X0
% 2.16/1.05      | k1_xboole_0 = X0 ),
% 2.16/1.05      inference(cnf_transformation,[],[f112]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1328,plain,
% 2.16/1.05      ( k2_enumset1(X0,X0,X1,X2) = X3
% 2.16/1.05      | k2_enumset1(X0,X0,X0,X2) = X3
% 2.16/1.05      | k2_enumset1(X1,X1,X1,X2) = X3
% 2.16/1.05      | k2_enumset1(X0,X0,X0,X1) = X3
% 2.16/1.05      | k2_enumset1(X2,X2,X2,X2) = X3
% 2.16/1.05      | k2_enumset1(X1,X1,X1,X1) = X3
% 2.16/1.05      | k2_enumset1(X0,X0,X0,X0) = X3
% 2.16/1.05      | k1_xboole_0 = X3
% 2.16/1.05      | r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) != iProver_top ),
% 2.16/1.05      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_3586,plain,
% 2.16/1.05      ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_relat_1(sK5)
% 2.16/1.05      | k1_relat_1(sK5) = k1_xboole_0 ),
% 2.16/1.05      inference(superposition,[status(thm)],[c_1630,c_1328]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_3711,plain,
% 2.16/1.05      ( k1_relat_1(sK5) = k1_xboole_0
% 2.16/1.05      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),sK4))) = iProver_top ),
% 2.16/1.05      inference(superposition,[status(thm)],[c_3586,c_1317]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_37,negated_conjecture,
% 2.16/1.05      ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) ),
% 2.16/1.05      inference(cnf_transformation,[],[f114]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_27,plain,
% 2.16/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.16/1.05      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.16/1.05      inference(cnf_transformation,[],[f87]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1588,plain,
% 2.16/1.05      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))
% 2.16/1.05      | k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_relat_1(sK5) ),
% 2.16/1.05      inference(instantiation,[status(thm)],[c_27]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_814,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1581,plain,
% 2.16/1.05      ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != X0
% 2.16/1.05      | k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) = k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5)
% 2.16/1.05      | k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) != X0 ),
% 2.16/1.05      inference(instantiation,[status(thm)],[c_814]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1667,plain,
% 2.16/1.05      ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) = k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5)
% 2.16/1.05      | k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relat_1(sK5)
% 2.16/1.05      | k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) != k2_relat_1(sK5) ),
% 2.16/1.05      inference(instantiation,[status(thm)],[c_1581]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_23,plain,
% 2.16/1.05      ( ~ v1_funct_1(X0)
% 2.16/1.05      | ~ v1_relat_1(X0)
% 2.16/1.05      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 2.16/1.05      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
% 2.16/1.05      inference(cnf_transformation,[],[f113]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_41,negated_conjecture,
% 2.16/1.05      ( v1_funct_1(sK5) ),
% 2.16/1.05      inference(cnf_transformation,[],[f97]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_415,plain,
% 2.16/1.05      ( ~ v1_relat_1(X0)
% 2.16/1.05      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 2.16/1.05      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
% 2.16/1.05      | sK5 != X0 ),
% 2.16/1.05      inference(resolution_lifted,[status(thm)],[c_23,c_41]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_416,plain,
% 2.16/1.05      ( ~ v1_relat_1(sK5)
% 2.16/1.05      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5)
% 2.16/1.05      | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5) ),
% 2.16/1.05      inference(unflattening,[status(thm)],[c_415]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1316,plain,
% 2.16/1.05      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5)
% 2.16/1.05      | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5)
% 2.16/1.05      | v1_relat_1(sK5) != iProver_top ),
% 2.16/1.05      inference(predicate_to_equality,[status(thm)],[c_416]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_44,plain,
% 2.16/1.05      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) = iProver_top ),
% 2.16/1.05      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_417,plain,
% 2.16/1.05      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5)
% 2.16/1.05      | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5)
% 2.16/1.05      | v1_relat_1(sK5) != iProver_top ),
% 2.16/1.05      inference(predicate_to_equality,[status(thm)],[c_416]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1561,plain,
% 2.16/1.05      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))
% 2.16/1.05      | v1_relat_1(sK5) ),
% 2.16/1.05      inference(instantiation,[status(thm)],[c_25]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1562,plain,
% 2.16/1.05      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) != iProver_top
% 2.16/1.05      | v1_relat_1(sK5) = iProver_top ),
% 2.16/1.05      inference(predicate_to_equality,[status(thm)],[c_1561]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1596,plain,
% 2.16/1.05      ( k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5)
% 2.16/1.05      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5) ),
% 2.16/1.05      inference(global_propositional_subsumption,
% 2.16/1.05                [status(thm)],
% 2.16/1.05                [c_1316,c_44,c_417,c_1562]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1597,plain,
% 2.16/1.05      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5)
% 2.16/1.05      | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5) ),
% 2.16/1.05      inference(renaming,[status(thm)],[c_1596]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_3702,plain,
% 2.16/1.05      ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) = k2_relat_1(sK5)
% 2.16/1.05      | k1_relat_1(sK5) = k1_xboole_0 ),
% 2.16/1.05      inference(superposition,[status(thm)],[c_3586,c_1597]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_4147,plain,
% 2.16/1.05      ( k1_relat_1(sK5) = k1_xboole_0 ),
% 2.16/1.05      inference(global_propositional_subsumption,
% 2.16/1.05                [status(thm)],
% 2.16/1.05                [c_3711,c_39,c_37,c_1588,c_1667,c_3702]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_22,plain,
% 2.16/1.05      ( ~ v1_relat_1(X0)
% 2.16/1.05      | k1_relat_1(X0) != k1_xboole_0
% 2.16/1.05      | k1_xboole_0 = X0 ),
% 2.16/1.05      inference(cnf_transformation,[],[f81]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1324,plain,
% 2.16/1.05      ( k1_relat_1(X0) != k1_xboole_0
% 2.16/1.05      | k1_xboole_0 = X0
% 2.16/1.05      | v1_relat_1(X0) != iProver_top ),
% 2.16/1.05      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_4165,plain,
% 2.16/1.05      ( sK5 = k1_xboole_0 | v1_relat_1(sK5) != iProver_top ),
% 2.16/1.05      inference(superposition,[status(thm)],[c_4147,c_1324]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1687,plain,
% 2.16/1.05      ( ~ v1_relat_1(sK5)
% 2.16/1.05      | k1_relat_1(sK5) != k1_xboole_0
% 2.16/1.05      | k1_xboole_0 = sK5 ),
% 2.16/1.05      inference(instantiation,[status(thm)],[c_22]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_813,plain,( X0 = X0 ),theory(equality) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1700,plain,
% 2.16/1.05      ( sK5 = sK5 ),
% 2.16/1.05      inference(instantiation,[status(thm)],[c_813]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_2001,plain,
% 2.16/1.05      ( X0 != X1 | sK5 != X1 | sK5 = X0 ),
% 2.16/1.05      inference(instantiation,[status(thm)],[c_814]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_3279,plain,
% 2.16/1.05      ( X0 != sK5 | sK5 = X0 | sK5 != sK5 ),
% 2.16/1.05      inference(instantiation,[status(thm)],[c_2001]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_3280,plain,
% 2.16/1.05      ( sK5 != sK5 | sK5 = k1_xboole_0 | k1_xboole_0 != sK5 ),
% 2.16/1.05      inference(instantiation,[status(thm)],[c_3279]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_4293,plain,
% 2.16/1.05      ( sK5 = k1_xboole_0 ),
% 2.16/1.05      inference(global_propositional_subsumption,
% 2.16/1.05                [status(thm)],
% 2.16/1.05                [c_4165,c_39,c_37,c_1561,c_1588,c_1667,c_1687,c_1700,
% 2.16/1.05                 c_3280,c_3702]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_36,plain,
% 2.16/1.05      ( ~ v1_funct_2(X0,X1,X2)
% 2.16/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.16/1.05      | k1_relset_1(X1,X2,X0) = X1
% 2.16/1.05      | k1_xboole_0 = X2 ),
% 2.16/1.05      inference(cnf_transformation,[],[f91]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_40,negated_conjecture,
% 2.16/1.05      ( v1_funct_2(sK5,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
% 2.16/1.05      inference(cnf_transformation,[],[f116]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_552,plain,
% 2.16/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.16/1.05      | k2_enumset1(sK3,sK3,sK3,sK3) != X1
% 2.16/1.05      | k1_relset_1(X1,X2,X0) = X1
% 2.16/1.05      | sK4 != X2
% 2.16/1.05      | sK5 != X0
% 2.16/1.05      | k1_xboole_0 = X2 ),
% 2.16/1.05      inference(resolution_lifted,[status(thm)],[c_36,c_40]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_553,plain,
% 2.16/1.05      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))
% 2.16/1.05      | k1_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_enumset1(sK3,sK3,sK3,sK3)
% 2.16/1.05      | k1_xboole_0 = sK4 ),
% 2.16/1.05      inference(unflattening,[status(thm)],[c_552]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_38,negated_conjecture,
% 2.16/1.05      ( k1_xboole_0 != sK4 ),
% 2.16/1.05      inference(cnf_transformation,[],[f100]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_555,plain,
% 2.16/1.05      ( k1_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 2.16/1.05      inference(global_propositional_subsumption,
% 2.16/1.05                [status(thm)],
% 2.16/1.05                [c_553,c_39,c_38]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_28,plain,
% 2.16/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.16/1.05      | ~ r2_hidden(X3,X1)
% 2.16/1.05      | r2_hidden(k4_tarski(X3,sK1(X0,X3)),X0)
% 2.16/1.05      | k1_relset_1(X1,X2,X0) != X1 ),
% 2.16/1.05      inference(cnf_transformation,[],[f90]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1320,plain,
% 2.16/1.05      ( k1_relset_1(X0,X1,X2) != X0
% 2.16/1.05      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.16/1.05      | r2_hidden(X3,X0) != iProver_top
% 2.16/1.05      | r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2) = iProver_top ),
% 2.16/1.05      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_3565,plain,
% 2.16/1.05      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) != iProver_top
% 2.16/1.05      | r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top
% 2.16/1.05      | r2_hidden(k4_tarski(X0,sK1(sK5,X0)),sK5) = iProver_top ),
% 2.16/1.05      inference(superposition,[status(thm)],[c_555,c_1320]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_4168,plain,
% 2.16/1.05      ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top
% 2.16/1.05      | r2_hidden(k4_tarski(X0,sK1(sK5,X0)),sK5) = iProver_top ),
% 2.16/1.05      inference(global_propositional_subsumption,
% 2.16/1.05                [status(thm)],
% 2.16/1.05                [c_3565,c_44]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_4296,plain,
% 2.16/1.05      ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top
% 2.16/1.05      | r2_hidden(k4_tarski(X0,sK1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top ),
% 2.16/1.05      inference(demodulation,[status(thm)],[c_4293,c_4168]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_4836,plain,
% 2.16/1.05      ( r2_hidden(k4_tarski(sK0(X0,X1),sK1(k1_xboole_0,sK0(X0,X1))),k1_xboole_0) = iProver_top
% 2.16/1.05      | r1_tarski(X0,X1) = iProver_top
% 2.16/1.05      | r1_tarski(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top ),
% 2.16/1.05      inference(superposition,[status(thm)],[c_3102,c_4296]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_24,plain,
% 2.16/1.05      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 2.16/1.05      inference(cnf_transformation,[],[f84]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1323,plain,
% 2.16/1.05      ( r2_hidden(X0,X1) != iProver_top
% 2.16/1.05      | r1_tarski(X1,X0) != iProver_top ),
% 2.16/1.05      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_4976,plain,
% 2.16/1.05      ( r1_tarski(X0,X1) = iProver_top
% 2.16/1.05      | r1_tarski(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top
% 2.16/1.05      | r1_tarski(k1_xboole_0,k4_tarski(sK0(X0,X1),sK1(k1_xboole_0,sK0(X0,X1)))) != iProver_top ),
% 2.16/1.05      inference(superposition,[status(thm)],[c_4836,c_1323]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_15,plain,
% 2.16/1.05      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.16/1.05      inference(cnf_transformation,[],[f75]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1327,plain,
% 2.16/1.05      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.16/1.05      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1672,plain,
% 2.16/1.05      ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top ),
% 2.16/1.05      inference(superposition,[status(thm)],[c_1327,c_1315]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_20,plain,
% 2.16/1.05      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.16/1.05      inference(cnf_transformation,[],[f79]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1673,plain,
% 2.16/1.05      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.16/1.05      inference(light_normalisation,[status(thm)],[c_1672,c_20]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_5453,plain,
% 2.16/1.05      ( r1_tarski(X0,X1) = iProver_top
% 2.16/1.05      | r1_tarski(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top ),
% 2.16/1.05      inference(forward_subsumption_resolution,
% 2.16/1.05                [status(thm)],
% 2.16/1.05                [c_4976,c_1673]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_5455,plain,
% 2.16/1.05      ( r1_tarski(k2_enumset1(sK3,sK3,sK3,sK3),X0) = iProver_top ),
% 2.16/1.05      inference(superposition,[status(thm)],[c_1337,c_5453]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_3,plain,
% 2.16/1.05      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 2.16/1.05      inference(cnf_transformation,[],[f62]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1338,plain,
% 2.16/1.05      ( X0 = X1
% 2.16/1.05      | r1_tarski(X0,X1) != iProver_top
% 2.16/1.05      | r1_tarski(X1,X0) != iProver_top ),
% 2.16/1.05      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_2957,plain,
% 2.16/1.05      ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_relat_1(sK5)
% 2.16/1.05      | r1_tarski(k2_enumset1(sK3,sK3,sK3,sK3),k1_relat_1(sK5)) != iProver_top ),
% 2.16/1.05      inference(superposition,[status(thm)],[c_1630,c_1338]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_4151,plain,
% 2.16/1.05      ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_xboole_0
% 2.16/1.05      | r1_tarski(k2_enumset1(sK3,sK3,sK3,sK3),k1_xboole_0) != iProver_top ),
% 2.16/1.05      inference(demodulation,[status(thm)],[c_4147,c_2957]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_5627,plain,
% 2.16/1.05      ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_xboole_0 ),
% 2.16/1.05      inference(superposition,[status(thm)],[c_5455,c_4151]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_4153,plain,
% 2.16/1.05      ( k2_enumset1(X0,X0,X0,X0) != k1_xboole_0
% 2.16/1.05      | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5) ),
% 2.16/1.05      inference(demodulation,[status(thm)],[c_4147,c_1597]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_19,plain,
% 2.16/1.05      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.16/1.05      inference(cnf_transformation,[],[f80]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_4526,plain,
% 2.16/1.05      ( k2_enumset1(X0,X0,X0,X0) != k1_xboole_0
% 2.16/1.05      | k2_enumset1(k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0)) = k1_xboole_0 ),
% 2.16/1.05      inference(light_normalisation,[status(thm)],[c_4153,c_19,c_4293]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_5838,plain,
% 2.16/1.05      ( k2_enumset1(k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3)) = k1_xboole_0 ),
% 2.16/1.05      inference(superposition,[status(thm)],[c_5627,c_4526]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1321,plain,
% 2.16/1.05      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.16/1.05      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.16/1.05      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_2601,plain,
% 2.16/1.05      ( k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_relat_1(sK5) ),
% 2.16/1.05      inference(superposition,[status(thm)],[c_1317,c_1321]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_2609,plain,
% 2.16/1.05      ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relat_1(sK5) ),
% 2.16/1.05      inference(demodulation,[status(thm)],[c_2601,c_37]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_4299,plain,
% 2.16/1.05      ( k2_enumset1(k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3)) != k2_relat_1(k1_xboole_0) ),
% 2.16/1.05      inference(demodulation,[status(thm)],[c_4293,c_2609]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_4317,plain,
% 2.16/1.05      ( k2_enumset1(k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3)) != k1_xboole_0 ),
% 2.16/1.05      inference(light_normalisation,[status(thm)],[c_4299,c_19]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(contradiction,plain,
% 2.16/1.05      ( $false ),
% 2.16/1.05      inference(minisat,[status(thm)],[c_5838,c_4317]) ).
% 2.16/1.05  
% 2.16/1.05  
% 2.16/1.05  % SZS output end CNFRefutation for theBenchmark.p
% 2.16/1.05  
% 2.16/1.05  ------                               Statistics
% 2.16/1.05  
% 2.16/1.05  ------ General
% 2.16/1.05  
% 2.16/1.05  abstr_ref_over_cycles:                  0
% 2.16/1.05  abstr_ref_under_cycles:                 0
% 2.16/1.05  gc_basic_clause_elim:                   0
% 2.16/1.05  forced_gc_time:                         0
% 2.16/1.05  parsing_time:                           0.012
% 2.16/1.05  unif_index_cands_time:                  0.
% 2.16/1.05  unif_index_add_time:                    0.
% 2.16/1.05  orderings_time:                         0.
% 2.16/1.05  out_proof_time:                         0.009
% 2.16/1.05  total_time:                             0.235
% 2.16/1.05  num_of_symbols:                         54
% 2.16/1.05  num_of_terms:                           6557
% 2.16/1.05  
% 2.16/1.05  ------ Preprocessing
% 2.16/1.05  
% 2.16/1.05  num_of_splits:                          0
% 2.16/1.05  num_of_split_atoms:                     0
% 2.16/1.05  num_of_reused_defs:                     0
% 2.16/1.05  num_eq_ax_congr_red:                    26
% 2.16/1.05  num_of_sem_filtered_clauses:            1
% 2.16/1.05  num_of_subtypes:                        0
% 2.16/1.05  monotx_restored_types:                  0
% 2.16/1.05  sat_num_of_epr_types:                   0
% 2.16/1.05  sat_num_of_non_cyclic_types:            0
% 2.16/1.05  sat_guarded_non_collapsed_types:        0
% 2.16/1.05  num_pure_diseq_elim:                    0
% 2.16/1.05  simp_replaced_by:                       0
% 2.16/1.05  res_preprocessed:                       174
% 2.16/1.05  prep_upred:                             0
% 2.16/1.05  prep_unflattend:                        30
% 2.16/1.05  smt_new_axioms:                         0
% 2.16/1.05  pred_elim_cands:                        4
% 2.16/1.05  pred_elim:                              3
% 2.16/1.05  pred_elim_cl:                           7
% 2.16/1.05  pred_elim_cycles:                       6
% 2.16/1.05  merged_defs:                            0
% 2.16/1.05  merged_defs_ncl:                        0
% 2.16/1.05  bin_hyper_res:                          0
% 2.16/1.05  prep_cycles:                            4
% 2.16/1.05  pred_elim_time:                         0.006
% 2.16/1.05  splitting_time:                         0.
% 2.16/1.05  sem_filter_time:                        0.
% 2.16/1.05  monotx_time:                            0.
% 2.16/1.05  subtype_inf_time:                       0.
% 2.16/1.05  
% 2.16/1.05  ------ Problem properties
% 2.16/1.05  
% 2.16/1.05  clauses:                                34
% 2.16/1.05  conjectures:                            3
% 2.16/1.05  epr:                                    5
% 2.16/1.05  horn:                                   30
% 2.16/1.05  ground:                                 8
% 2.16/1.05  unary:                                  16
% 2.16/1.05  binary:                                 6
% 2.16/1.05  lits:                                   72
% 2.16/1.05  lits_eq:                                29
% 2.16/1.05  fd_pure:                                0
% 2.16/1.05  fd_pseudo:                              0
% 2.16/1.05  fd_cond:                                2
% 2.16/1.05  fd_pseudo_cond:                         2
% 2.16/1.05  ac_symbols:                             0
% 2.16/1.05  
% 2.16/1.05  ------ Propositional Solver
% 2.16/1.05  
% 2.16/1.05  prop_solver_calls:                      27
% 2.16/1.05  prop_fast_solver_calls:                 1034
% 2.16/1.05  smt_solver_calls:                       0
% 2.16/1.05  smt_fast_solver_calls:                  0
% 2.16/1.05  prop_num_of_clauses:                    2215
% 2.16/1.05  prop_preprocess_simplified:             7832
% 2.16/1.05  prop_fo_subsumed:                       20
% 2.16/1.05  prop_solver_time:                       0.
% 2.16/1.05  smt_solver_time:                        0.
% 2.16/1.05  smt_fast_solver_time:                   0.
% 2.16/1.05  prop_fast_solver_time:                  0.
% 2.16/1.05  prop_unsat_core_time:                   0.
% 2.16/1.05  
% 2.16/1.05  ------ QBF
% 2.16/1.05  
% 2.16/1.05  qbf_q_res:                              0
% 2.16/1.05  qbf_num_tautologies:                    0
% 2.16/1.05  qbf_prep_cycles:                        0
% 2.16/1.05  
% 2.16/1.05  ------ BMC1
% 2.16/1.05  
% 2.16/1.05  bmc1_current_bound:                     -1
% 2.16/1.05  bmc1_last_solved_bound:                 -1
% 2.16/1.05  bmc1_unsat_core_size:                   -1
% 2.16/1.05  bmc1_unsat_core_parents_size:           -1
% 2.16/1.05  bmc1_merge_next_fun:                    0
% 2.16/1.05  bmc1_unsat_core_clauses_time:           0.
% 2.16/1.05  
% 2.16/1.05  ------ Instantiation
% 2.16/1.05  
% 2.16/1.05  inst_num_of_clauses:                    679
% 2.16/1.05  inst_num_in_passive:                    170
% 2.16/1.05  inst_num_in_active:                     257
% 2.16/1.05  inst_num_in_unprocessed:                252
% 2.16/1.05  inst_num_of_loops:                      370
% 2.16/1.05  inst_num_of_learning_restarts:          0
% 2.16/1.05  inst_num_moves_active_passive:          111
% 2.16/1.05  inst_lit_activity:                      0
% 2.16/1.05  inst_lit_activity_moves:                0
% 2.16/1.05  inst_num_tautologies:                   0
% 2.16/1.05  inst_num_prop_implied:                  0
% 2.16/1.05  inst_num_existing_simplified:           0
% 2.16/1.05  inst_num_eq_res_simplified:             0
% 2.16/1.05  inst_num_child_elim:                    0
% 2.16/1.05  inst_num_of_dismatching_blockings:      169
% 2.16/1.05  inst_num_of_non_proper_insts:           511
% 2.16/1.05  inst_num_of_duplicates:                 0
% 2.16/1.05  inst_inst_num_from_inst_to_res:         0
% 2.16/1.05  inst_dismatching_checking_time:         0.
% 2.16/1.05  
% 2.16/1.05  ------ Resolution
% 2.16/1.05  
% 2.16/1.05  res_num_of_clauses:                     0
% 2.16/1.05  res_num_in_passive:                     0
% 2.16/1.05  res_num_in_active:                      0
% 2.16/1.05  res_num_of_loops:                       178
% 2.16/1.05  res_forward_subset_subsumed:            65
% 2.16/1.05  res_backward_subset_subsumed:           0
% 2.16/1.05  res_forward_subsumed:                   0
% 2.16/1.05  res_backward_subsumed:                  0
% 2.16/1.05  res_forward_subsumption_resolution:     0
% 2.16/1.05  res_backward_subsumption_resolution:    0
% 2.16/1.05  res_clause_to_clause_subsumption:       447
% 2.16/1.05  res_orphan_elimination:                 0
% 2.16/1.05  res_tautology_del:                      34
% 2.16/1.05  res_num_eq_res_simplified:              0
% 2.16/1.05  res_num_sel_changes:                    0
% 2.16/1.05  res_moves_from_active_to_pass:          0
% 2.16/1.05  
% 2.16/1.05  ------ Superposition
% 2.16/1.05  
% 2.16/1.05  sup_time_total:                         0.
% 2.16/1.05  sup_time_generating:                    0.
% 2.16/1.05  sup_time_sim_full:                      0.
% 2.16/1.05  sup_time_sim_immed:                     0.
% 2.16/1.05  
% 2.16/1.05  sup_num_of_clauses:                     72
% 2.16/1.05  sup_num_in_active:                      49
% 2.16/1.05  sup_num_in_passive:                     23
% 2.16/1.05  sup_num_of_loops:                       73
% 2.16/1.05  sup_fw_superposition:                   96
% 2.16/1.05  sup_bw_superposition:                   92
% 2.16/1.05  sup_immediate_simplified:               31
% 2.16/1.05  sup_given_eliminated:                   1
% 2.16/1.05  comparisons_done:                       0
% 2.16/1.05  comparisons_avoided:                    0
% 2.16/1.05  
% 2.16/1.05  ------ Simplifications
% 2.16/1.05  
% 2.16/1.05  
% 2.16/1.05  sim_fw_subset_subsumed:                 9
% 2.16/1.05  sim_bw_subset_subsumed:                 15
% 2.16/1.05  sim_fw_subsumed:                        21
% 2.16/1.05  sim_bw_subsumed:                        0
% 2.16/1.05  sim_fw_subsumption_res:                 2
% 2.16/1.05  sim_bw_subsumption_res:                 0
% 2.16/1.05  sim_tautology_del:                      2
% 2.16/1.05  sim_eq_tautology_del:                   26
% 2.16/1.05  sim_eq_res_simp:                        0
% 2.16/1.05  sim_fw_demodulated:                     0
% 2.16/1.05  sim_bw_demodulated:                     23
% 2.16/1.05  sim_light_normalised:                   13
% 2.16/1.05  sim_joinable_taut:                      0
% 2.16/1.05  sim_joinable_simp:                      0
% 2.16/1.05  sim_ac_normalised:                      0
% 2.16/1.05  sim_smt_subsumption:                    0
% 2.16/1.05  
%------------------------------------------------------------------------------
