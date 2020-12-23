%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:06:08 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 225 expanded)
%              Number of clauses        :   39 (  41 expanded)
%              Number of leaves         :   18 (  58 expanded)
%              Depth                    :   20
%              Number of atoms          :  297 ( 593 expanded)
%              Number of equality atoms :  140 ( 262 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f26,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f27,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f26])).

fof(f33,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(X3,X2) != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
   => ( k1_funct_1(sK4,sK3) != sK2
      & r2_hidden(sK3,sK1)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))
      & v1_funct_2(sK4,sK1,k1_tarski(sK2))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( k1_funct_1(sK4,sK3) != sK2
    & r2_hidden(sK3,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))
    & v1_funct_2(sK4,sK1,k1_tarski(sK2))
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f27,f33])).

fof(f61,plain,(
    r2_hidden(sK3,sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f60,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f45,f46])).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f44,f63])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f43,f64])).

fof(f66,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f42,f65])).

fof(f67,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f41,f66])).

fof(f68,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f40,f67])).

fof(f73,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    inference(definition_unfolding,[],[f60,f68])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X2),X0)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f58,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f59,plain,(
    v1_funct_2(sK4,sK1,k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f34])).

fof(f74,plain,(
    v1_funct_2(sK4,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(definition_unfolding,[],[f59,f68])).

fof(f15,axiom,(
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

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ~ v1_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : ~ v1_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f10])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK0(X0,X1) != X0
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( sK0(X0,X1) = X0
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK0(X0,X1) != X0
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( sK0(X0,X1) = X0
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f72,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f36,f68])).

fof(f77,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f72])).

fof(f62,plain,(
    k1_funct_1(sK4,sK3) != sK2 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_17,negated_conjecture,
    ( r2_hidden(sK3,sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_659,plain,
    ( r2_hidden(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v5_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_6,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X2),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_234,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X2),X1)
    | ~ v1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_20])).

cnf(c_235,plain,
    ( ~ v5_relat_1(sK4,X0)
    | ~ r2_hidden(X1,k1_relat_1(sK4))
    | r2_hidden(k1_funct_1(sK4,X1),X0)
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_234])).

cnf(c_257,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(sK4))
    | r2_hidden(k1_funct_1(sK4,X3),X4)
    | ~ v1_relat_1(sK4)
    | X4 != X2
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_235])).

cnf(c_258,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r2_hidden(X2,k1_relat_1(sK4))
    | r2_hidden(k1_funct_1(sK4,X2),X1)
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_257])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_270,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r2_hidden(X2,k1_relat_1(sK4))
    | r2_hidden(k1_funct_1(sK4,X2),X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_258,c_7])).

cnf(c_391,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | r2_hidden(k1_funct_1(sK4,X0),X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X2,X1))
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_270])).

cnf(c_496,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | r2_hidden(k1_funct_1(sK4,X0),X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X2,X1)) ),
    inference(equality_resolution_simp,[status(thm)],[c_391])).

cnf(c_658,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | r2_hidden(X2,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_496])).

cnf(c_1154,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_658])).

cnf(c_19,negated_conjecture,
    ( v1_funct_2(sK4,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_281,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_18])).

cnf(c_282,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | k1_relset_1(X0,X1,sK4) = X0
    | k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_281])).

cnf(c_451,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != X0
    | k1_relset_1(X1,X0,sK4) = X1
    | k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0))
    | sK1 != X1
    | sK4 != sK4
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_282])).

cnf(c_452,plain,
    ( k1_relset_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK4) = sK1
    | k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))
    | k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(unflattening,[status(thm)],[c_451])).

cnf(c_495,plain,
    ( k1_relset_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK4) = sK1
    | k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(equality_resolution_simp,[status(thm)],[c_452])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_317,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_18])).

cnf(c_318,plain,
    ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_317])).

cnf(c_762,plain,
    ( k1_relset_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK4) = k1_relat_1(sK4) ),
    inference(equality_resolution,[status(thm)],[c_318])).

cnf(c_841,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_xboole_0
    | k1_relat_1(sK4) = sK1 ),
    inference(demodulation,[status(thm)],[c_495,c_762])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_5,plain,
    ( ~ v1_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_228,plain,
    ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_5])).

cnf(c_980,plain,
    ( k1_relat_1(sK4) = sK1 ),
    inference(superposition,[status(thm)],[c_841,c_228])).

cnf(c_1439,plain,
    ( r2_hidden(X0,sK1) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1154,c_980])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_660,plain,
    ( X0 = X1
    | r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1446,plain,
    ( k1_funct_1(sK4,X0) = sK2
    | r2_hidden(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1439,c_660])).

cnf(c_1953,plain,
    ( k1_funct_1(sK4,sK3) = sK2 ),
    inference(superposition,[status(thm)],[c_659,c_1446])).

cnf(c_16,negated_conjecture,
    ( k1_funct_1(sK4,sK3) != sK2 ),
    inference(cnf_transformation,[],[f62])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1953,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:26:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.24/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.03  
% 2.24/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.24/1.03  
% 2.24/1.03  ------  iProver source info
% 2.24/1.03  
% 2.24/1.03  git: date: 2020-06-30 10:37:57 +0100
% 2.24/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.24/1.03  git: non_committed_changes: false
% 2.24/1.03  git: last_make_outside_of_git: false
% 2.24/1.03  
% 2.24/1.03  ------ 
% 2.24/1.03  
% 2.24/1.03  ------ Input Options
% 2.24/1.03  
% 2.24/1.03  --out_options                           all
% 2.24/1.03  --tptp_safe_out                         true
% 2.24/1.03  --problem_path                          ""
% 2.24/1.03  --include_path                          ""
% 2.24/1.03  --clausifier                            res/vclausify_rel
% 2.24/1.03  --clausifier_options                    --mode clausify
% 2.24/1.03  --stdin                                 false
% 2.24/1.03  --stats_out                             all
% 2.24/1.03  
% 2.24/1.03  ------ General Options
% 2.24/1.03  
% 2.24/1.03  --fof                                   false
% 2.24/1.03  --time_out_real                         305.
% 2.24/1.03  --time_out_virtual                      -1.
% 2.24/1.03  --symbol_type_check                     false
% 2.24/1.03  --clausify_out                          false
% 2.24/1.03  --sig_cnt_out                           false
% 2.24/1.03  --trig_cnt_out                          false
% 2.24/1.03  --trig_cnt_out_tolerance                1.
% 2.24/1.03  --trig_cnt_out_sk_spl                   false
% 2.24/1.03  --abstr_cl_out                          false
% 2.24/1.03  
% 2.24/1.03  ------ Global Options
% 2.24/1.03  
% 2.24/1.03  --schedule                              default
% 2.24/1.03  --add_important_lit                     false
% 2.24/1.03  --prop_solver_per_cl                    1000
% 2.24/1.03  --min_unsat_core                        false
% 2.24/1.03  --soft_assumptions                      false
% 2.24/1.03  --soft_lemma_size                       3
% 2.24/1.03  --prop_impl_unit_size                   0
% 2.24/1.03  --prop_impl_unit                        []
% 2.24/1.03  --share_sel_clauses                     true
% 2.24/1.03  --reset_solvers                         false
% 2.24/1.03  --bc_imp_inh                            [conj_cone]
% 2.24/1.03  --conj_cone_tolerance                   3.
% 2.24/1.03  --extra_neg_conj                        none
% 2.24/1.03  --large_theory_mode                     true
% 2.24/1.03  --prolific_symb_bound                   200
% 2.24/1.03  --lt_threshold                          2000
% 2.24/1.03  --clause_weak_htbl                      true
% 2.24/1.03  --gc_record_bc_elim                     false
% 2.24/1.03  
% 2.24/1.03  ------ Preprocessing Options
% 2.24/1.03  
% 2.24/1.03  --preprocessing_flag                    true
% 2.24/1.03  --time_out_prep_mult                    0.1
% 2.24/1.03  --splitting_mode                        input
% 2.24/1.03  --splitting_grd                         true
% 2.24/1.03  --splitting_cvd                         false
% 2.24/1.03  --splitting_cvd_svl                     false
% 2.24/1.03  --splitting_nvd                         32
% 2.24/1.03  --sub_typing                            true
% 2.24/1.03  --prep_gs_sim                           true
% 2.24/1.03  --prep_unflatten                        true
% 2.24/1.03  --prep_res_sim                          true
% 2.24/1.03  --prep_upred                            true
% 2.24/1.03  --prep_sem_filter                       exhaustive
% 2.24/1.03  --prep_sem_filter_out                   false
% 2.24/1.03  --pred_elim                             true
% 2.24/1.03  --res_sim_input                         true
% 2.24/1.03  --eq_ax_congr_red                       true
% 2.24/1.03  --pure_diseq_elim                       true
% 2.24/1.03  --brand_transform                       false
% 2.24/1.03  --non_eq_to_eq                          false
% 2.24/1.03  --prep_def_merge                        true
% 2.24/1.03  --prep_def_merge_prop_impl              false
% 2.24/1.03  --prep_def_merge_mbd                    true
% 2.24/1.03  --prep_def_merge_tr_red                 false
% 2.24/1.03  --prep_def_merge_tr_cl                  false
% 2.24/1.03  --smt_preprocessing                     true
% 2.24/1.03  --smt_ac_axioms                         fast
% 2.24/1.03  --preprocessed_out                      false
% 2.24/1.03  --preprocessed_stats                    false
% 2.24/1.03  
% 2.24/1.03  ------ Abstraction refinement Options
% 2.24/1.03  
% 2.24/1.03  --abstr_ref                             []
% 2.24/1.03  --abstr_ref_prep                        false
% 2.24/1.03  --abstr_ref_until_sat                   false
% 2.24/1.03  --abstr_ref_sig_restrict                funpre
% 2.24/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.24/1.03  --abstr_ref_under                       []
% 2.24/1.03  
% 2.24/1.03  ------ SAT Options
% 2.24/1.03  
% 2.24/1.03  --sat_mode                              false
% 2.24/1.03  --sat_fm_restart_options                ""
% 2.24/1.03  --sat_gr_def                            false
% 2.24/1.03  --sat_epr_types                         true
% 2.24/1.03  --sat_non_cyclic_types                  false
% 2.24/1.03  --sat_finite_models                     false
% 2.24/1.03  --sat_fm_lemmas                         false
% 2.24/1.03  --sat_fm_prep                           false
% 2.24/1.03  --sat_fm_uc_incr                        true
% 2.24/1.03  --sat_out_model                         small
% 2.24/1.03  --sat_out_clauses                       false
% 2.24/1.03  
% 2.24/1.03  ------ QBF Options
% 2.24/1.03  
% 2.24/1.03  --qbf_mode                              false
% 2.24/1.03  --qbf_elim_univ                         false
% 2.24/1.03  --qbf_dom_inst                          none
% 2.24/1.03  --qbf_dom_pre_inst                      false
% 2.24/1.03  --qbf_sk_in                             false
% 2.24/1.03  --qbf_pred_elim                         true
% 2.24/1.03  --qbf_split                             512
% 2.24/1.03  
% 2.24/1.03  ------ BMC1 Options
% 2.24/1.03  
% 2.24/1.03  --bmc1_incremental                      false
% 2.24/1.03  --bmc1_axioms                           reachable_all
% 2.24/1.03  --bmc1_min_bound                        0
% 2.24/1.03  --bmc1_max_bound                        -1
% 2.24/1.03  --bmc1_max_bound_default                -1
% 2.24/1.03  --bmc1_symbol_reachability              true
% 2.24/1.03  --bmc1_property_lemmas                  false
% 2.24/1.03  --bmc1_k_induction                      false
% 2.24/1.03  --bmc1_non_equiv_states                 false
% 2.24/1.03  --bmc1_deadlock                         false
% 2.24/1.03  --bmc1_ucm                              false
% 2.24/1.03  --bmc1_add_unsat_core                   none
% 2.24/1.03  --bmc1_unsat_core_children              false
% 2.24/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.24/1.03  --bmc1_out_stat                         full
% 2.24/1.03  --bmc1_ground_init                      false
% 2.24/1.03  --bmc1_pre_inst_next_state              false
% 2.24/1.03  --bmc1_pre_inst_state                   false
% 2.24/1.03  --bmc1_pre_inst_reach_state             false
% 2.24/1.03  --bmc1_out_unsat_core                   false
% 2.24/1.03  --bmc1_aig_witness_out                  false
% 2.24/1.03  --bmc1_verbose                          false
% 2.24/1.03  --bmc1_dump_clauses_tptp                false
% 2.24/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.24/1.03  --bmc1_dump_file                        -
% 2.24/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.24/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.24/1.03  --bmc1_ucm_extend_mode                  1
% 2.24/1.03  --bmc1_ucm_init_mode                    2
% 2.24/1.03  --bmc1_ucm_cone_mode                    none
% 2.24/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.24/1.03  --bmc1_ucm_relax_model                  4
% 2.24/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.24/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.24/1.03  --bmc1_ucm_layered_model                none
% 2.24/1.03  --bmc1_ucm_max_lemma_size               10
% 2.24/1.03  
% 2.24/1.03  ------ AIG Options
% 2.24/1.03  
% 2.24/1.03  --aig_mode                              false
% 2.24/1.03  
% 2.24/1.03  ------ Instantiation Options
% 2.24/1.03  
% 2.24/1.03  --instantiation_flag                    true
% 2.24/1.03  --inst_sos_flag                         false
% 2.24/1.03  --inst_sos_phase                        true
% 2.24/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.24/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.24/1.03  --inst_lit_sel_side                     num_symb
% 2.24/1.03  --inst_solver_per_active                1400
% 2.24/1.03  --inst_solver_calls_frac                1.
% 2.24/1.03  --inst_passive_queue_type               priority_queues
% 2.24/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.24/1.03  --inst_passive_queues_freq              [25;2]
% 2.24/1.03  --inst_dismatching                      true
% 2.24/1.03  --inst_eager_unprocessed_to_passive     true
% 2.24/1.03  --inst_prop_sim_given                   true
% 2.24/1.03  --inst_prop_sim_new                     false
% 2.24/1.03  --inst_subs_new                         false
% 2.24/1.03  --inst_eq_res_simp                      false
% 2.24/1.03  --inst_subs_given                       false
% 2.24/1.03  --inst_orphan_elimination               true
% 2.24/1.03  --inst_learning_loop_flag               true
% 2.24/1.03  --inst_learning_start                   3000
% 2.24/1.03  --inst_learning_factor                  2
% 2.24/1.03  --inst_start_prop_sim_after_learn       3
% 2.24/1.03  --inst_sel_renew                        solver
% 2.24/1.03  --inst_lit_activity_flag                true
% 2.24/1.03  --inst_restr_to_given                   false
% 2.24/1.03  --inst_activity_threshold               500
% 2.24/1.03  --inst_out_proof                        true
% 2.24/1.03  
% 2.24/1.03  ------ Resolution Options
% 2.24/1.03  
% 2.24/1.03  --resolution_flag                       true
% 2.24/1.03  --res_lit_sel                           adaptive
% 2.24/1.03  --res_lit_sel_side                      none
% 2.24/1.03  --res_ordering                          kbo
% 2.24/1.03  --res_to_prop_solver                    active
% 2.24/1.03  --res_prop_simpl_new                    false
% 2.24/1.03  --res_prop_simpl_given                  true
% 2.24/1.03  --res_passive_queue_type                priority_queues
% 2.24/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.24/1.03  --res_passive_queues_freq               [15;5]
% 2.24/1.03  --res_forward_subs                      full
% 2.24/1.03  --res_backward_subs                     full
% 2.24/1.03  --res_forward_subs_resolution           true
% 2.24/1.03  --res_backward_subs_resolution          true
% 2.24/1.03  --res_orphan_elimination                true
% 2.24/1.03  --res_time_limit                        2.
% 2.24/1.03  --res_out_proof                         true
% 2.24/1.03  
% 2.24/1.03  ------ Superposition Options
% 2.24/1.03  
% 2.24/1.03  --superposition_flag                    true
% 2.24/1.03  --sup_passive_queue_type                priority_queues
% 2.24/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.24/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.24/1.03  --demod_completeness_check              fast
% 2.24/1.03  --demod_use_ground                      true
% 2.24/1.03  --sup_to_prop_solver                    passive
% 2.24/1.03  --sup_prop_simpl_new                    true
% 2.24/1.03  --sup_prop_simpl_given                  true
% 2.24/1.03  --sup_fun_splitting                     false
% 2.24/1.03  --sup_smt_interval                      50000
% 2.24/1.03  
% 2.24/1.03  ------ Superposition Simplification Setup
% 2.24/1.03  
% 2.24/1.03  --sup_indices_passive                   []
% 2.24/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.24/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.24/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.24/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.24/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.24/1.03  --sup_full_bw                           [BwDemod]
% 2.24/1.03  --sup_immed_triv                        [TrivRules]
% 2.24/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.24/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.24/1.03  --sup_immed_bw_main                     []
% 2.24/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.24/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.24/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.24/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.24/1.03  
% 2.24/1.03  ------ Combination Options
% 2.24/1.03  
% 2.24/1.03  --comb_res_mult                         3
% 2.24/1.03  --comb_sup_mult                         2
% 2.24/1.03  --comb_inst_mult                        10
% 2.24/1.03  
% 2.24/1.03  ------ Debug Options
% 2.24/1.03  
% 2.24/1.03  --dbg_backtrace                         false
% 2.24/1.03  --dbg_dump_prop_clauses                 false
% 2.24/1.03  --dbg_dump_prop_clauses_file            -
% 2.24/1.03  --dbg_out_stat                          false
% 2.24/1.03  ------ Parsing...
% 2.24/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.24/1.03  
% 2.24/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.24/1.03  
% 2.24/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.24/1.03  
% 2.24/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.24/1.03  ------ Proving...
% 2.24/1.03  ------ Problem Properties 
% 2.24/1.03  
% 2.24/1.03  
% 2.24/1.03  clauses                                 11
% 2.24/1.03  conjectures                             2
% 2.24/1.03  EPR                                     1
% 2.24/1.03  Horn                                    9
% 2.24/1.03  unary                                   4
% 2.24/1.03  binary                                  3
% 2.24/1.03  lits                                    22
% 2.24/1.03  lits eq                                 15
% 2.24/1.03  fd_pure                                 0
% 2.24/1.03  fd_pseudo                               0
% 2.24/1.03  fd_cond                                 0
% 2.24/1.03  fd_pseudo_cond                          2
% 2.24/1.03  AC symbols                              0
% 2.24/1.03  
% 2.24/1.03  ------ Schedule dynamic 5 is on 
% 2.24/1.03  
% 2.24/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.24/1.03  
% 2.24/1.03  
% 2.24/1.03  ------ 
% 2.24/1.03  Current options:
% 2.24/1.03  ------ 
% 2.24/1.03  
% 2.24/1.03  ------ Input Options
% 2.24/1.03  
% 2.24/1.03  --out_options                           all
% 2.24/1.03  --tptp_safe_out                         true
% 2.24/1.03  --problem_path                          ""
% 2.24/1.03  --include_path                          ""
% 2.24/1.03  --clausifier                            res/vclausify_rel
% 2.24/1.03  --clausifier_options                    --mode clausify
% 2.24/1.03  --stdin                                 false
% 2.24/1.03  --stats_out                             all
% 2.24/1.03  
% 2.24/1.03  ------ General Options
% 2.24/1.03  
% 2.24/1.03  --fof                                   false
% 2.24/1.03  --time_out_real                         305.
% 2.24/1.03  --time_out_virtual                      -1.
% 2.24/1.03  --symbol_type_check                     false
% 2.24/1.03  --clausify_out                          false
% 2.24/1.03  --sig_cnt_out                           false
% 2.24/1.03  --trig_cnt_out                          false
% 2.24/1.03  --trig_cnt_out_tolerance                1.
% 2.24/1.03  --trig_cnt_out_sk_spl                   false
% 2.24/1.03  --abstr_cl_out                          false
% 2.24/1.03  
% 2.24/1.03  ------ Global Options
% 2.24/1.03  
% 2.24/1.03  --schedule                              default
% 2.24/1.03  --add_important_lit                     false
% 2.24/1.03  --prop_solver_per_cl                    1000
% 2.24/1.03  --min_unsat_core                        false
% 2.24/1.03  --soft_assumptions                      false
% 2.24/1.03  --soft_lemma_size                       3
% 2.24/1.03  --prop_impl_unit_size                   0
% 2.24/1.03  --prop_impl_unit                        []
% 2.24/1.03  --share_sel_clauses                     true
% 2.24/1.03  --reset_solvers                         false
% 2.24/1.03  --bc_imp_inh                            [conj_cone]
% 2.24/1.03  --conj_cone_tolerance                   3.
% 2.24/1.03  --extra_neg_conj                        none
% 2.24/1.03  --large_theory_mode                     true
% 2.24/1.03  --prolific_symb_bound                   200
% 2.24/1.03  --lt_threshold                          2000
% 2.24/1.03  --clause_weak_htbl                      true
% 2.24/1.03  --gc_record_bc_elim                     false
% 2.24/1.03  
% 2.24/1.03  ------ Preprocessing Options
% 2.24/1.03  
% 2.24/1.03  --preprocessing_flag                    true
% 2.24/1.03  --time_out_prep_mult                    0.1
% 2.24/1.03  --splitting_mode                        input
% 2.24/1.03  --splitting_grd                         true
% 2.24/1.03  --splitting_cvd                         false
% 2.24/1.03  --splitting_cvd_svl                     false
% 2.24/1.03  --splitting_nvd                         32
% 2.24/1.03  --sub_typing                            true
% 2.24/1.03  --prep_gs_sim                           true
% 2.24/1.03  --prep_unflatten                        true
% 2.24/1.03  --prep_res_sim                          true
% 2.24/1.03  --prep_upred                            true
% 2.24/1.03  --prep_sem_filter                       exhaustive
% 2.24/1.03  --prep_sem_filter_out                   false
% 2.24/1.03  --pred_elim                             true
% 2.24/1.03  --res_sim_input                         true
% 2.24/1.03  --eq_ax_congr_red                       true
% 2.24/1.03  --pure_diseq_elim                       true
% 2.24/1.03  --brand_transform                       false
% 2.24/1.03  --non_eq_to_eq                          false
% 2.24/1.03  --prep_def_merge                        true
% 2.24/1.03  --prep_def_merge_prop_impl              false
% 2.24/1.03  --prep_def_merge_mbd                    true
% 2.24/1.03  --prep_def_merge_tr_red                 false
% 2.24/1.03  --prep_def_merge_tr_cl                  false
% 2.24/1.03  --smt_preprocessing                     true
% 2.24/1.03  --smt_ac_axioms                         fast
% 2.24/1.03  --preprocessed_out                      false
% 2.24/1.03  --preprocessed_stats                    false
% 2.24/1.03  
% 2.24/1.03  ------ Abstraction refinement Options
% 2.24/1.03  
% 2.24/1.03  --abstr_ref                             []
% 2.24/1.03  --abstr_ref_prep                        false
% 2.24/1.03  --abstr_ref_until_sat                   false
% 2.24/1.03  --abstr_ref_sig_restrict                funpre
% 2.24/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.24/1.03  --abstr_ref_under                       []
% 2.24/1.03  
% 2.24/1.03  ------ SAT Options
% 2.24/1.03  
% 2.24/1.03  --sat_mode                              false
% 2.24/1.03  --sat_fm_restart_options                ""
% 2.24/1.03  --sat_gr_def                            false
% 2.24/1.03  --sat_epr_types                         true
% 2.24/1.03  --sat_non_cyclic_types                  false
% 2.24/1.03  --sat_finite_models                     false
% 2.24/1.03  --sat_fm_lemmas                         false
% 2.24/1.03  --sat_fm_prep                           false
% 2.24/1.03  --sat_fm_uc_incr                        true
% 2.24/1.03  --sat_out_model                         small
% 2.24/1.03  --sat_out_clauses                       false
% 2.24/1.03  
% 2.24/1.03  ------ QBF Options
% 2.24/1.03  
% 2.24/1.03  --qbf_mode                              false
% 2.24/1.03  --qbf_elim_univ                         false
% 2.24/1.03  --qbf_dom_inst                          none
% 2.24/1.03  --qbf_dom_pre_inst                      false
% 2.24/1.03  --qbf_sk_in                             false
% 2.24/1.03  --qbf_pred_elim                         true
% 2.24/1.03  --qbf_split                             512
% 2.24/1.03  
% 2.24/1.03  ------ BMC1 Options
% 2.24/1.03  
% 2.24/1.03  --bmc1_incremental                      false
% 2.24/1.03  --bmc1_axioms                           reachable_all
% 2.24/1.03  --bmc1_min_bound                        0
% 2.24/1.03  --bmc1_max_bound                        -1
% 2.24/1.03  --bmc1_max_bound_default                -1
% 2.24/1.03  --bmc1_symbol_reachability              true
% 2.24/1.03  --bmc1_property_lemmas                  false
% 2.24/1.03  --bmc1_k_induction                      false
% 2.24/1.03  --bmc1_non_equiv_states                 false
% 2.24/1.03  --bmc1_deadlock                         false
% 2.24/1.03  --bmc1_ucm                              false
% 2.24/1.03  --bmc1_add_unsat_core                   none
% 2.24/1.03  --bmc1_unsat_core_children              false
% 2.24/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.24/1.03  --bmc1_out_stat                         full
% 2.24/1.03  --bmc1_ground_init                      false
% 2.24/1.03  --bmc1_pre_inst_next_state              false
% 2.24/1.03  --bmc1_pre_inst_state                   false
% 2.24/1.03  --bmc1_pre_inst_reach_state             false
% 2.24/1.03  --bmc1_out_unsat_core                   false
% 2.24/1.03  --bmc1_aig_witness_out                  false
% 2.24/1.03  --bmc1_verbose                          false
% 2.24/1.03  --bmc1_dump_clauses_tptp                false
% 2.24/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.24/1.03  --bmc1_dump_file                        -
% 2.24/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.24/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.24/1.03  --bmc1_ucm_extend_mode                  1
% 2.24/1.03  --bmc1_ucm_init_mode                    2
% 2.24/1.03  --bmc1_ucm_cone_mode                    none
% 2.24/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.24/1.03  --bmc1_ucm_relax_model                  4
% 2.24/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.24/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.24/1.03  --bmc1_ucm_layered_model                none
% 2.24/1.03  --bmc1_ucm_max_lemma_size               10
% 2.24/1.03  
% 2.24/1.03  ------ AIG Options
% 2.24/1.03  
% 2.24/1.03  --aig_mode                              false
% 2.24/1.03  
% 2.24/1.03  ------ Instantiation Options
% 2.24/1.03  
% 2.24/1.03  --instantiation_flag                    true
% 2.24/1.03  --inst_sos_flag                         false
% 2.24/1.03  --inst_sos_phase                        true
% 2.24/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.24/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.24/1.03  --inst_lit_sel_side                     none
% 2.24/1.03  --inst_solver_per_active                1400
% 2.24/1.03  --inst_solver_calls_frac                1.
% 2.24/1.03  --inst_passive_queue_type               priority_queues
% 2.24/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.24/1.03  --inst_passive_queues_freq              [25;2]
% 2.24/1.03  --inst_dismatching                      true
% 2.24/1.03  --inst_eager_unprocessed_to_passive     true
% 2.24/1.03  --inst_prop_sim_given                   true
% 2.24/1.03  --inst_prop_sim_new                     false
% 2.24/1.03  --inst_subs_new                         false
% 2.24/1.03  --inst_eq_res_simp                      false
% 2.24/1.03  --inst_subs_given                       false
% 2.24/1.03  --inst_orphan_elimination               true
% 2.24/1.03  --inst_learning_loop_flag               true
% 2.24/1.03  --inst_learning_start                   3000
% 2.24/1.03  --inst_learning_factor                  2
% 2.24/1.03  --inst_start_prop_sim_after_learn       3
% 2.24/1.03  --inst_sel_renew                        solver
% 2.24/1.03  --inst_lit_activity_flag                true
% 2.24/1.03  --inst_restr_to_given                   false
% 2.24/1.03  --inst_activity_threshold               500
% 2.24/1.03  --inst_out_proof                        true
% 2.24/1.03  
% 2.24/1.03  ------ Resolution Options
% 2.24/1.03  
% 2.24/1.03  --resolution_flag                       false
% 2.24/1.03  --res_lit_sel                           adaptive
% 2.24/1.03  --res_lit_sel_side                      none
% 2.24/1.03  --res_ordering                          kbo
% 2.24/1.03  --res_to_prop_solver                    active
% 2.24/1.03  --res_prop_simpl_new                    false
% 2.24/1.03  --res_prop_simpl_given                  true
% 2.24/1.03  --res_passive_queue_type                priority_queues
% 2.24/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.24/1.03  --res_passive_queues_freq               [15;5]
% 2.24/1.03  --res_forward_subs                      full
% 2.24/1.03  --res_backward_subs                     full
% 2.24/1.03  --res_forward_subs_resolution           true
% 2.24/1.03  --res_backward_subs_resolution          true
% 2.24/1.03  --res_orphan_elimination                true
% 2.24/1.03  --res_time_limit                        2.
% 2.24/1.03  --res_out_proof                         true
% 2.24/1.03  
% 2.24/1.03  ------ Superposition Options
% 2.24/1.03  
% 2.24/1.03  --superposition_flag                    true
% 2.24/1.03  --sup_passive_queue_type                priority_queues
% 2.24/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.24/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.24/1.03  --demod_completeness_check              fast
% 2.24/1.03  --demod_use_ground                      true
% 2.24/1.03  --sup_to_prop_solver                    passive
% 2.24/1.03  --sup_prop_simpl_new                    true
% 2.24/1.03  --sup_prop_simpl_given                  true
% 2.24/1.03  --sup_fun_splitting                     false
% 2.24/1.03  --sup_smt_interval                      50000
% 2.24/1.03  
% 2.24/1.03  ------ Superposition Simplification Setup
% 2.24/1.03  
% 2.24/1.03  --sup_indices_passive                   []
% 2.24/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.24/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.24/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.24/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.24/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.24/1.03  --sup_full_bw                           [BwDemod]
% 2.24/1.03  --sup_immed_triv                        [TrivRules]
% 2.24/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.24/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.24/1.03  --sup_immed_bw_main                     []
% 2.24/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.24/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.24/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.24/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.24/1.03  
% 2.24/1.03  ------ Combination Options
% 2.24/1.03  
% 2.24/1.03  --comb_res_mult                         3
% 2.24/1.03  --comb_sup_mult                         2
% 2.24/1.03  --comb_inst_mult                        10
% 2.24/1.03  
% 2.24/1.03  ------ Debug Options
% 2.24/1.03  
% 2.24/1.03  --dbg_backtrace                         false
% 2.24/1.03  --dbg_dump_prop_clauses                 false
% 2.24/1.03  --dbg_dump_prop_clauses_file            -
% 2.24/1.03  --dbg_out_stat                          false
% 2.24/1.03  
% 2.24/1.03  
% 2.24/1.03  
% 2.24/1.03  
% 2.24/1.03  ------ Proving...
% 2.24/1.03  
% 2.24/1.03  
% 2.24/1.03  % SZS status Theorem for theBenchmark.p
% 2.24/1.03  
% 2.24/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 2.24/1.03  
% 2.24/1.03  fof(f16,conjecture,(
% 2.24/1.03    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 2.24/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.24/1.03  
% 2.24/1.03  fof(f17,negated_conjecture,(
% 2.24/1.03    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 2.24/1.03    inference(negated_conjecture,[],[f16])).
% 2.24/1.03  
% 2.24/1.03  fof(f26,plain,(
% 2.24/1.03    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 2.24/1.03    inference(ennf_transformation,[],[f17])).
% 2.24/1.03  
% 2.24/1.03  fof(f27,plain,(
% 2.24/1.03    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 2.24/1.03    inference(flattening,[],[f26])).
% 2.24/1.03  
% 2.24/1.03  fof(f33,plain,(
% 2.24/1.03    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (k1_funct_1(sK4,sK3) != sK2 & r2_hidden(sK3,sK1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) & v1_funct_2(sK4,sK1,k1_tarski(sK2)) & v1_funct_1(sK4))),
% 2.24/1.03    introduced(choice_axiom,[])).
% 2.24/1.03  
% 2.24/1.03  fof(f34,plain,(
% 2.24/1.03    k1_funct_1(sK4,sK3) != sK2 & r2_hidden(sK3,sK1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) & v1_funct_2(sK4,sK1,k1_tarski(sK2)) & v1_funct_1(sK4)),
% 2.24/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f27,f33])).
% 2.24/1.03  
% 2.24/1.03  fof(f61,plain,(
% 2.24/1.03    r2_hidden(sK3,sK1)),
% 2.24/1.03    inference(cnf_transformation,[],[f34])).
% 2.24/1.03  
% 2.24/1.03  fof(f60,plain,(
% 2.24/1.03    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))),
% 2.24/1.03    inference(cnf_transformation,[],[f34])).
% 2.24/1.03  
% 2.24/1.03  fof(f3,axiom,(
% 2.24/1.03    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 2.24/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.24/1.03  
% 2.24/1.03  fof(f40,plain,(
% 2.24/1.03    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 2.24/1.03    inference(cnf_transformation,[],[f3])).
% 2.24/1.03  
% 2.24/1.03  fof(f4,axiom,(
% 2.24/1.03    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.24/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.24/1.03  
% 2.24/1.03  fof(f41,plain,(
% 2.24/1.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.24/1.03    inference(cnf_transformation,[],[f4])).
% 2.24/1.03  
% 2.24/1.03  fof(f5,axiom,(
% 2.24/1.03    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.24/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.24/1.03  
% 2.24/1.03  fof(f42,plain,(
% 2.24/1.03    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.24/1.03    inference(cnf_transformation,[],[f5])).
% 2.24/1.03  
% 2.24/1.03  fof(f6,axiom,(
% 2.24/1.03    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.24/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.24/1.03  
% 2.24/1.03  fof(f43,plain,(
% 2.24/1.03    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.24/1.03    inference(cnf_transformation,[],[f6])).
% 2.24/1.03  
% 2.24/1.03  fof(f7,axiom,(
% 2.24/1.03    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.24/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.24/1.03  
% 2.24/1.03  fof(f44,plain,(
% 2.24/1.03    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.24/1.03    inference(cnf_transformation,[],[f7])).
% 2.24/1.03  
% 2.24/1.03  fof(f8,axiom,(
% 2.24/1.03    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.24/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.24/1.03  
% 2.24/1.03  fof(f45,plain,(
% 2.24/1.03    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.24/1.03    inference(cnf_transformation,[],[f8])).
% 2.24/1.03  
% 2.24/1.03  fof(f9,axiom,(
% 2.24/1.03    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 2.24/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.24/1.03  
% 2.24/1.03  fof(f46,plain,(
% 2.24/1.03    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 2.24/1.03    inference(cnf_transformation,[],[f9])).
% 2.24/1.03  
% 2.24/1.03  fof(f63,plain,(
% 2.24/1.03    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.24/1.03    inference(definition_unfolding,[],[f45,f46])).
% 2.24/1.03  
% 2.24/1.03  fof(f64,plain,(
% 2.24/1.03    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.24/1.03    inference(definition_unfolding,[],[f44,f63])).
% 2.24/1.03  
% 2.24/1.03  fof(f65,plain,(
% 2.24/1.03    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.24/1.03    inference(definition_unfolding,[],[f43,f64])).
% 2.24/1.03  
% 2.24/1.03  fof(f66,plain,(
% 2.24/1.03    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.24/1.03    inference(definition_unfolding,[],[f42,f65])).
% 2.24/1.03  
% 2.24/1.03  fof(f67,plain,(
% 2.24/1.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.24/1.03    inference(definition_unfolding,[],[f41,f66])).
% 2.24/1.03  
% 2.24/1.03  fof(f68,plain,(
% 2.24/1.03    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.24/1.03    inference(definition_unfolding,[],[f40,f67])).
% 2.24/1.03  
% 2.24/1.03  fof(f73,plain,(
% 2.24/1.03    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))),
% 2.24/1.03    inference(definition_unfolding,[],[f60,f68])).
% 2.24/1.03  
% 2.24/1.03  fof(f13,axiom,(
% 2.24/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.24/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.24/1.03  
% 2.24/1.03  fof(f18,plain,(
% 2.24/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.24/1.03    inference(pure_predicate_removal,[],[f13])).
% 2.24/1.03  
% 2.24/1.03  fof(f22,plain,(
% 2.24/1.03    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.24/1.03    inference(ennf_transformation,[],[f18])).
% 2.24/1.03  
% 2.24/1.03  fof(f50,plain,(
% 2.24/1.03    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.24/1.03    inference(cnf_transformation,[],[f22])).
% 2.24/1.03  
% 2.24/1.03  fof(f11,axiom,(
% 2.24/1.03    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 2.24/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.24/1.03  
% 2.24/1.03  fof(f19,plain,(
% 2.24/1.03    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.24/1.03    inference(ennf_transformation,[],[f11])).
% 2.24/1.03  
% 2.24/1.03  fof(f20,plain,(
% 2.24/1.03    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.24/1.03    inference(flattening,[],[f19])).
% 2.24/1.03  
% 2.24/1.03  fof(f48,plain,(
% 2.24/1.03    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.24/1.03    inference(cnf_transformation,[],[f20])).
% 2.24/1.03  
% 2.24/1.03  fof(f58,plain,(
% 2.24/1.03    v1_funct_1(sK4)),
% 2.24/1.03    inference(cnf_transformation,[],[f34])).
% 2.24/1.03  
% 2.24/1.03  fof(f12,axiom,(
% 2.24/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.24/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.24/1.03  
% 2.24/1.03  fof(f21,plain,(
% 2.24/1.03    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.24/1.03    inference(ennf_transformation,[],[f12])).
% 2.24/1.03  
% 2.24/1.03  fof(f49,plain,(
% 2.24/1.03    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.24/1.03    inference(cnf_transformation,[],[f21])).
% 2.24/1.03  
% 2.24/1.03  fof(f59,plain,(
% 2.24/1.03    v1_funct_2(sK4,sK1,k1_tarski(sK2))),
% 2.24/1.03    inference(cnf_transformation,[],[f34])).
% 2.24/1.03  
% 2.24/1.03  fof(f74,plain,(
% 2.24/1.03    v1_funct_2(sK4,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),
% 2.24/1.03    inference(definition_unfolding,[],[f59,f68])).
% 2.24/1.03  
% 2.24/1.03  fof(f15,axiom,(
% 2.24/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.24/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.24/1.03  
% 2.24/1.03  fof(f24,plain,(
% 2.24/1.03    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.24/1.03    inference(ennf_transformation,[],[f15])).
% 2.24/1.03  
% 2.24/1.03  fof(f25,plain,(
% 2.24/1.03    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.24/1.03    inference(flattening,[],[f24])).
% 2.24/1.03  
% 2.24/1.03  fof(f32,plain,(
% 2.24/1.03    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.24/1.03    inference(nnf_transformation,[],[f25])).
% 2.24/1.03  
% 2.24/1.03  fof(f52,plain,(
% 2.24/1.03    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.24/1.03    inference(cnf_transformation,[],[f32])).
% 2.24/1.03  
% 2.24/1.03  fof(f14,axiom,(
% 2.24/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.24/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.24/1.03  
% 2.24/1.03  fof(f23,plain,(
% 2.24/1.03    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.24/1.03    inference(ennf_transformation,[],[f14])).
% 2.24/1.03  
% 2.24/1.03  fof(f51,plain,(
% 2.24/1.03    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.24/1.03    inference(cnf_transformation,[],[f23])).
% 2.24/1.03  
% 2.24/1.03  fof(f1,axiom,(
% 2.24/1.03    v1_xboole_0(k1_xboole_0)),
% 2.24/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.24/1.03  
% 2.24/1.03  fof(f35,plain,(
% 2.24/1.03    v1_xboole_0(k1_xboole_0)),
% 2.24/1.03    inference(cnf_transformation,[],[f1])).
% 2.24/1.03  
% 2.24/1.03  fof(f10,axiom,(
% 2.24/1.03    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ~v1_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))),
% 2.24/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.24/1.03  
% 2.24/1.03  fof(f47,plain,(
% 2.24/1.03    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (~v1_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))) )),
% 2.24/1.03    inference(cnf_transformation,[],[f10])).
% 2.24/1.03  
% 2.24/1.03  fof(f2,axiom,(
% 2.24/1.03    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.24/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.24/1.03  
% 2.24/1.03  fof(f28,plain,(
% 2.24/1.03    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.24/1.03    inference(nnf_transformation,[],[f2])).
% 2.24/1.03  
% 2.24/1.03  fof(f29,plain,(
% 2.24/1.03    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.24/1.03    inference(rectify,[],[f28])).
% 2.24/1.03  
% 2.24/1.03  fof(f30,plain,(
% 2.24/1.03    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1))))),
% 2.24/1.03    introduced(choice_axiom,[])).
% 2.24/1.03  
% 2.24/1.03  fof(f31,plain,(
% 2.24/1.03    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.24/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 2.24/1.03  
% 2.24/1.03  fof(f36,plain,(
% 2.24/1.03    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 2.24/1.03    inference(cnf_transformation,[],[f31])).
% 2.24/1.03  
% 2.24/1.03  fof(f72,plain,(
% 2.24/1.03    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 2.24/1.03    inference(definition_unfolding,[],[f36,f68])).
% 2.24/1.03  
% 2.24/1.03  fof(f77,plain,(
% 2.24/1.03    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) )),
% 2.24/1.03    inference(equality_resolution,[],[f72])).
% 2.24/1.03  
% 2.24/1.03  fof(f62,plain,(
% 2.24/1.03    k1_funct_1(sK4,sK3) != sK2),
% 2.24/1.03    inference(cnf_transformation,[],[f34])).
% 2.24/1.03  
% 2.24/1.03  cnf(c_17,negated_conjecture,
% 2.24/1.03      ( r2_hidden(sK3,sK1) ),
% 2.24/1.03      inference(cnf_transformation,[],[f61]) ).
% 2.24/1.03  
% 2.24/1.03  cnf(c_659,plain,
% 2.24/1.03      ( r2_hidden(sK3,sK1) = iProver_top ),
% 2.24/1.03      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.24/1.03  
% 2.24/1.03  cnf(c_18,negated_conjecture,
% 2.24/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
% 2.24/1.03      inference(cnf_transformation,[],[f73]) ).
% 2.24/1.03  
% 2.24/1.03  cnf(c_8,plain,
% 2.24/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.24/1.03      | v5_relat_1(X0,X2) ),
% 2.24/1.03      inference(cnf_transformation,[],[f50]) ).
% 2.24/1.03  
% 2.24/1.03  cnf(c_6,plain,
% 2.24/1.03      ( ~ v5_relat_1(X0,X1)
% 2.24/1.03      | ~ r2_hidden(X2,k1_relat_1(X0))
% 2.24/1.03      | r2_hidden(k1_funct_1(X0,X2),X1)
% 2.24/1.03      | ~ v1_relat_1(X0)
% 2.24/1.03      | ~ v1_funct_1(X0) ),
% 2.24/1.03      inference(cnf_transformation,[],[f48]) ).
% 2.24/1.03  
% 2.24/1.03  cnf(c_20,negated_conjecture,
% 2.24/1.03      ( v1_funct_1(sK4) ),
% 2.24/1.03      inference(cnf_transformation,[],[f58]) ).
% 2.24/1.03  
% 2.24/1.03  cnf(c_234,plain,
% 2.24/1.03      ( ~ v5_relat_1(X0,X1)
% 2.24/1.03      | ~ r2_hidden(X2,k1_relat_1(X0))
% 2.24/1.03      | r2_hidden(k1_funct_1(X0,X2),X1)
% 2.24/1.03      | ~ v1_relat_1(X0)
% 2.24/1.03      | sK4 != X0 ),
% 2.24/1.03      inference(resolution_lifted,[status(thm)],[c_6,c_20]) ).
% 2.24/1.03  
% 2.24/1.03  cnf(c_235,plain,
% 2.24/1.03      ( ~ v5_relat_1(sK4,X0)
% 2.24/1.03      | ~ r2_hidden(X1,k1_relat_1(sK4))
% 2.24/1.03      | r2_hidden(k1_funct_1(sK4,X1),X0)
% 2.24/1.03      | ~ v1_relat_1(sK4) ),
% 2.24/1.03      inference(unflattening,[status(thm)],[c_234]) ).
% 2.24/1.03  
% 2.24/1.03  cnf(c_257,plain,
% 2.24/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.24/1.03      | ~ r2_hidden(X3,k1_relat_1(sK4))
% 2.24/1.03      | r2_hidden(k1_funct_1(sK4,X3),X4)
% 2.24/1.03      | ~ v1_relat_1(sK4)
% 2.24/1.03      | X4 != X2
% 2.24/1.03      | sK4 != X0 ),
% 2.24/1.03      inference(resolution_lifted,[status(thm)],[c_8,c_235]) ).
% 2.24/1.03  
% 2.24/1.03  cnf(c_258,plain,
% 2.24/1.03      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.24/1.03      | ~ r2_hidden(X2,k1_relat_1(sK4))
% 2.24/1.03      | r2_hidden(k1_funct_1(sK4,X2),X1)
% 2.24/1.03      | ~ v1_relat_1(sK4) ),
% 2.24/1.03      inference(unflattening,[status(thm)],[c_257]) ).
% 2.24/1.03  
% 2.24/1.03  cnf(c_7,plain,
% 2.24/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.24/1.03      | v1_relat_1(X0) ),
% 2.24/1.03      inference(cnf_transformation,[],[f49]) ).
% 2.24/1.03  
% 2.24/1.03  cnf(c_270,plain,
% 2.24/1.03      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.24/1.03      | ~ r2_hidden(X2,k1_relat_1(sK4))
% 2.24/1.03      | r2_hidden(k1_funct_1(sK4,X2),X1) ),
% 2.24/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_258,c_7]) ).
% 2.24/1.03  
% 2.24/1.03  cnf(c_391,plain,
% 2.24/1.03      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 2.24/1.03      | r2_hidden(k1_funct_1(sK4,X0),X1)
% 2.24/1.03      | k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X2,X1))
% 2.24/1.03      | sK4 != sK4 ),
% 2.24/1.03      inference(resolution_lifted,[status(thm)],[c_18,c_270]) ).
% 2.24/1.03  
% 2.24/1.03  cnf(c_496,plain,
% 2.24/1.03      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 2.24/1.03      | r2_hidden(k1_funct_1(sK4,X0),X1)
% 2.24/1.03      | k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X2,X1)) ),
% 2.24/1.03      inference(equality_resolution_simp,[status(thm)],[c_391]) ).
% 2.24/1.03  
% 2.24/1.03  cnf(c_658,plain,
% 2.24/1.03      ( k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.24/1.03      | r2_hidden(X2,k1_relat_1(sK4)) != iProver_top
% 2.24/1.03      | r2_hidden(k1_funct_1(sK4,X2),X1) = iProver_top ),
% 2.24/1.03      inference(predicate_to_equality,[status(thm)],[c_496]) ).
% 2.24/1.03  
% 2.24/1.03  cnf(c_1154,plain,
% 2.24/1.03      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.24/1.03      | r2_hidden(k1_funct_1(sK4,X0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
% 2.24/1.03      inference(equality_resolution,[status(thm)],[c_658]) ).
% 2.24/1.03  
% 2.24/1.03  cnf(c_19,negated_conjecture,
% 2.24/1.03      ( v1_funct_2(sK4,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
% 2.24/1.03      inference(cnf_transformation,[],[f74]) ).
% 2.24/1.03  
% 2.24/1.03  cnf(c_15,plain,
% 2.24/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 2.24/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.24/1.03      | k1_relset_1(X1,X2,X0) = X1
% 2.24/1.03      | k1_xboole_0 = X2 ),
% 2.24/1.03      inference(cnf_transformation,[],[f52]) ).
% 2.24/1.03  
% 2.24/1.03  cnf(c_281,plain,
% 2.24/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 2.24/1.03      | k1_relset_1(X1,X2,X0) = X1
% 2.24/1.03      | k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 2.24/1.03      | sK4 != X0
% 2.24/1.03      | k1_xboole_0 = X2 ),
% 2.24/1.03      inference(resolution_lifted,[status(thm)],[c_15,c_18]) ).
% 2.24/1.03  
% 2.24/1.03  cnf(c_282,plain,
% 2.24/1.03      ( ~ v1_funct_2(sK4,X0,X1)
% 2.24/1.03      | k1_relset_1(X0,X1,sK4) = X0
% 2.24/1.03      | k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.24/1.03      | k1_xboole_0 = X1 ),
% 2.24/1.03      inference(unflattening,[status(thm)],[c_281]) ).
% 2.24/1.03  
% 2.24/1.03  cnf(c_451,plain,
% 2.24/1.03      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != X0
% 2.24/1.03      | k1_relset_1(X1,X0,sK4) = X1
% 2.24/1.03      | k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0))
% 2.24/1.03      | sK1 != X1
% 2.24/1.03      | sK4 != sK4
% 2.24/1.03      | k1_xboole_0 = X0 ),
% 2.24/1.03      inference(resolution_lifted,[status(thm)],[c_19,c_282]) ).
% 2.24/1.03  
% 2.24/1.03  cnf(c_452,plain,
% 2.24/1.03      ( k1_relset_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK4) = sK1
% 2.24/1.03      | k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))
% 2.24/1.03      | k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 2.24/1.03      inference(unflattening,[status(thm)],[c_451]) ).
% 2.24/1.03  
% 2.24/1.03  cnf(c_495,plain,
% 2.24/1.03      ( k1_relset_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK4) = sK1
% 2.24/1.03      | k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 2.24/1.03      inference(equality_resolution_simp,[status(thm)],[c_452]) ).
% 2.24/1.03  
% 2.24/1.03  cnf(c_9,plain,
% 2.24/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.24/1.03      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.24/1.03      inference(cnf_transformation,[],[f51]) ).
% 2.24/1.03  
% 2.24/1.03  cnf(c_317,plain,
% 2.24/1.03      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.24/1.03      | k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.24/1.03      | sK4 != X2 ),
% 2.24/1.03      inference(resolution_lifted,[status(thm)],[c_9,c_18]) ).
% 2.24/1.03  
% 2.24/1.03  cnf(c_318,plain,
% 2.24/1.03      ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
% 2.24/1.03      | k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.24/1.03      inference(unflattening,[status(thm)],[c_317]) ).
% 2.24/1.03  
% 2.24/1.03  cnf(c_762,plain,
% 2.24/1.03      ( k1_relset_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK4) = k1_relat_1(sK4) ),
% 2.24/1.03      inference(equality_resolution,[status(thm)],[c_318]) ).
% 2.24/1.03  
% 2.24/1.03  cnf(c_841,plain,
% 2.24/1.03      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_xboole_0
% 2.24/1.03      | k1_relat_1(sK4) = sK1 ),
% 2.24/1.03      inference(demodulation,[status(thm)],[c_495,c_762]) ).
% 2.24/1.03  
% 2.24/1.03  cnf(c_0,plain,
% 2.24/1.03      ( v1_xboole_0(k1_xboole_0) ),
% 2.24/1.03      inference(cnf_transformation,[],[f35]) ).
% 2.24/1.03  
% 2.24/1.03  cnf(c_5,plain,
% 2.24/1.03      ( ~ v1_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
% 2.24/1.03      inference(cnf_transformation,[],[f47]) ).
% 2.24/1.03  
% 2.24/1.03  cnf(c_228,plain,
% 2.24/1.03      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k1_xboole_0 ),
% 2.24/1.03      inference(resolution_lifted,[status(thm)],[c_0,c_5]) ).
% 2.24/1.03  
% 2.24/1.03  cnf(c_980,plain,
% 2.24/1.03      ( k1_relat_1(sK4) = sK1 ),
% 2.24/1.03      inference(superposition,[status(thm)],[c_841,c_228]) ).
% 2.24/1.03  
% 2.24/1.03  cnf(c_1439,plain,
% 2.24/1.03      ( r2_hidden(X0,sK1) != iProver_top
% 2.24/1.03      | r2_hidden(k1_funct_1(sK4,X0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
% 2.24/1.03      inference(light_normalisation,[status(thm)],[c_1154,c_980]) ).
% 2.24/1.03  
% 2.24/1.03  cnf(c_4,plain,
% 2.24/1.03      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | X0 = X1 ),
% 2.24/1.03      inference(cnf_transformation,[],[f77]) ).
% 2.24/1.03  
% 2.24/1.03  cnf(c_660,plain,
% 2.24/1.03      ( X0 = X1
% 2.24/1.03      | r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != iProver_top ),
% 2.24/1.03      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.24/1.03  
% 2.24/1.03  cnf(c_1446,plain,
% 2.24/1.03      ( k1_funct_1(sK4,X0) = sK2 | r2_hidden(X0,sK1) != iProver_top ),
% 2.24/1.03      inference(superposition,[status(thm)],[c_1439,c_660]) ).
% 2.24/1.03  
% 2.24/1.03  cnf(c_1953,plain,
% 2.24/1.03      ( k1_funct_1(sK4,sK3) = sK2 ),
% 2.24/1.03      inference(superposition,[status(thm)],[c_659,c_1446]) ).
% 2.24/1.03  
% 2.24/1.03  cnf(c_16,negated_conjecture,
% 2.24/1.03      ( k1_funct_1(sK4,sK3) != sK2 ),
% 2.24/1.03      inference(cnf_transformation,[],[f62]) ).
% 2.24/1.03  
% 2.24/1.03  cnf(contradiction,plain,
% 2.24/1.03      ( $false ),
% 2.24/1.03      inference(minisat,[status(thm)],[c_1953,c_16]) ).
% 2.24/1.03  
% 2.24/1.03  
% 2.24/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.24/1.03  
% 2.24/1.03  ------                               Statistics
% 2.24/1.03  
% 2.24/1.03  ------ General
% 2.24/1.03  
% 2.24/1.03  abstr_ref_over_cycles:                  0
% 2.24/1.03  abstr_ref_under_cycles:                 0
% 2.24/1.03  gc_basic_clause_elim:                   0
% 2.24/1.03  forced_gc_time:                         0
% 2.24/1.03  parsing_time:                           0.007
% 2.24/1.03  unif_index_cands_time:                  0.
% 2.24/1.03  unif_index_add_time:                    0.
% 2.24/1.03  orderings_time:                         0.
% 2.24/1.03  out_proof_time:                         0.007
% 2.24/1.03  total_time:                             0.072
% 2.24/1.03  num_of_symbols:                         50
% 2.24/1.03  num_of_terms:                           2030
% 2.24/1.03  
% 2.24/1.03  ------ Preprocessing
% 2.24/1.03  
% 2.24/1.03  num_of_splits:                          0
% 2.24/1.03  num_of_split_atoms:                     0
% 2.24/1.03  num_of_reused_defs:                     0
% 2.24/1.03  num_eq_ax_congr_red:                    12
% 2.24/1.03  num_of_sem_filtered_clauses:            1
% 2.24/1.03  num_of_subtypes:                        0
% 2.24/1.03  monotx_restored_types:                  0
% 2.24/1.03  sat_num_of_epr_types:                   0
% 2.24/1.03  sat_num_of_non_cyclic_types:            0
% 2.24/1.03  sat_guarded_non_collapsed_types:        0
% 2.24/1.03  num_pure_diseq_elim:                    0
% 2.24/1.03  simp_replaced_by:                       0
% 2.24/1.03  res_preprocessed:                       73
% 2.24/1.03  prep_upred:                             0
% 2.24/1.03  prep_unflattend:                        26
% 2.24/1.03  smt_new_axioms:                         0
% 2.24/1.03  pred_elim_cands:                        1
% 2.24/1.03  pred_elim:                              6
% 2.24/1.03  pred_elim_cl:                           10
% 2.24/1.03  pred_elim_cycles:                       8
% 2.24/1.03  merged_defs:                            0
% 2.24/1.03  merged_defs_ncl:                        0
% 2.24/1.03  bin_hyper_res:                          0
% 2.24/1.03  prep_cycles:                            4
% 2.24/1.03  pred_elim_time:                         0.004
% 2.24/1.03  splitting_time:                         0.
% 2.24/1.03  sem_filter_time:                        0.
% 2.24/1.03  monotx_time:                            0.
% 2.24/1.03  subtype_inf_time:                       0.
% 2.24/1.03  
% 2.24/1.03  ------ Problem properties
% 2.24/1.03  
% 2.24/1.03  clauses:                                11
% 2.24/1.03  conjectures:                            2
% 2.24/1.03  epr:                                    1
% 2.24/1.03  horn:                                   9
% 2.24/1.03  ground:                                 4
% 2.24/1.03  unary:                                  4
% 2.24/1.03  binary:                                 3
% 2.24/1.03  lits:                                   22
% 2.24/1.03  lits_eq:                                15
% 2.24/1.03  fd_pure:                                0
% 2.24/1.03  fd_pseudo:                              0
% 2.24/1.03  fd_cond:                                0
% 2.24/1.03  fd_pseudo_cond:                         2
% 2.24/1.03  ac_symbols:                             0
% 2.24/1.03  
% 2.24/1.03  ------ Propositional Solver
% 2.24/1.03  
% 2.24/1.03  prop_solver_calls:                      27
% 2.24/1.03  prop_fast_solver_calls:                 457
% 2.24/1.03  smt_solver_calls:                       0
% 2.24/1.03  smt_fast_solver_calls:                  0
% 2.24/1.03  prop_num_of_clauses:                    675
% 2.24/1.03  prop_preprocess_simplified:             2329
% 2.24/1.03  prop_fo_subsumed:                       4
% 2.24/1.03  prop_solver_time:                       0.
% 2.24/1.03  smt_solver_time:                        0.
% 2.24/1.03  smt_fast_solver_time:                   0.
% 2.24/1.03  prop_fast_solver_time:                  0.
% 2.24/1.03  prop_unsat_core_time:                   0.
% 2.24/1.03  
% 2.24/1.03  ------ QBF
% 2.24/1.03  
% 2.24/1.03  qbf_q_res:                              0
% 2.24/1.03  qbf_num_tautologies:                    0
% 2.24/1.03  qbf_prep_cycles:                        0
% 2.24/1.03  
% 2.24/1.03  ------ BMC1
% 2.24/1.03  
% 2.24/1.03  bmc1_current_bound:                     -1
% 2.24/1.03  bmc1_last_solved_bound:                 -1
% 2.24/1.03  bmc1_unsat_core_size:                   -1
% 2.24/1.03  bmc1_unsat_core_parents_size:           -1
% 2.24/1.03  bmc1_merge_next_fun:                    0
% 2.24/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.24/1.03  
% 2.24/1.03  ------ Instantiation
% 2.24/1.03  
% 2.24/1.03  inst_num_of_clauses:                    201
% 2.24/1.03  inst_num_in_passive:                    76
% 2.24/1.03  inst_num_in_active:                     101
% 2.24/1.03  inst_num_in_unprocessed:                24
% 2.24/1.03  inst_num_of_loops:                      110
% 2.24/1.03  inst_num_of_learning_restarts:          0
% 2.24/1.03  inst_num_moves_active_passive:          6
% 2.24/1.03  inst_lit_activity:                      0
% 2.24/1.03  inst_lit_activity_moves:                0
% 2.24/1.03  inst_num_tautologies:                   0
% 2.24/1.03  inst_num_prop_implied:                  0
% 2.24/1.03  inst_num_existing_simplified:           0
% 2.24/1.03  inst_num_eq_res_simplified:             0
% 2.24/1.03  inst_num_child_elim:                    0
% 2.24/1.03  inst_num_of_dismatching_blockings:      43
% 2.24/1.03  inst_num_of_non_proper_insts:           196
% 2.24/1.03  inst_num_of_duplicates:                 0
% 2.24/1.03  inst_inst_num_from_inst_to_res:         0
% 2.24/1.03  inst_dismatching_checking_time:         0.
% 2.24/1.03  
% 2.24/1.03  ------ Resolution
% 2.24/1.03  
% 2.24/1.03  res_num_of_clauses:                     0
% 2.24/1.03  res_num_in_passive:                     0
% 2.24/1.03  res_num_in_active:                      0
% 2.24/1.03  res_num_of_loops:                       77
% 2.24/1.03  res_forward_subset_subsumed:            23
% 2.24/1.03  res_backward_subset_subsumed:           0
% 2.24/1.03  res_forward_subsumed:                   1
% 2.24/1.03  res_backward_subsumed:                  0
% 2.24/1.03  res_forward_subsumption_resolution:     1
% 2.24/1.03  res_backward_subsumption_resolution:    0
% 2.24/1.03  res_clause_to_clause_subsumption:       271
% 2.24/1.03  res_orphan_elimination:                 0
% 2.24/1.03  res_tautology_del:                      18
% 2.24/1.03  res_num_eq_res_simplified:              2
% 2.24/1.03  res_num_sel_changes:                    0
% 2.24/1.03  res_moves_from_active_to_pass:          0
% 2.24/1.03  
% 2.24/1.03  ------ Superposition
% 2.24/1.03  
% 2.24/1.03  sup_time_total:                         0.
% 2.24/1.03  sup_time_generating:                    0.
% 2.24/1.03  sup_time_sim_full:                      0.
% 2.24/1.03  sup_time_sim_immed:                     0.
% 2.24/1.03  
% 2.24/1.03  sup_num_of_clauses:                     43
% 2.24/1.03  sup_num_in_active:                      16
% 2.24/1.03  sup_num_in_passive:                     27
% 2.24/1.03  sup_num_of_loops:                       20
% 2.24/1.03  sup_fw_superposition:                   26
% 2.24/1.03  sup_bw_superposition:                   37
% 2.24/1.03  sup_immediate_simplified:               18
% 2.24/1.03  sup_given_eliminated:                   0
% 2.24/1.03  comparisons_done:                       0
% 2.24/1.03  comparisons_avoided:                    7
% 2.24/1.03  
% 2.24/1.03  ------ Simplifications
% 2.24/1.03  
% 2.24/1.03  
% 2.24/1.03  sim_fw_subset_subsumed:                 13
% 2.24/1.03  sim_bw_subset_subsumed:                 0
% 2.24/1.03  sim_fw_subsumed:                        5
% 2.24/1.03  sim_bw_subsumed:                        0
% 2.24/1.03  sim_fw_subsumption_res:                 1
% 2.24/1.03  sim_bw_subsumption_res:                 0
% 2.24/1.03  sim_tautology_del:                      0
% 2.24/1.03  sim_eq_tautology_del:                   3
% 2.24/1.03  sim_eq_res_simp:                        0
% 2.24/1.03  sim_fw_demodulated:                     1
% 2.24/1.03  sim_bw_demodulated:                     5
% 2.24/1.03  sim_light_normalised:                   1
% 2.24/1.03  sim_joinable_taut:                      0
% 2.24/1.03  sim_joinable_simp:                      0
% 2.24/1.03  sim_ac_normalised:                      0
% 2.24/1.03  sim_smt_subsumption:                    0
% 2.24/1.03  
%------------------------------------------------------------------------------
