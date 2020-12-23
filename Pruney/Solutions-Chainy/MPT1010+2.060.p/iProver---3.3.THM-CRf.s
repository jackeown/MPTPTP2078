%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:06:13 EST 2020

% Result     : Theorem 2.99s
% Output     : CNFRefutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 283 expanded)
%              Number of clauses        :   58 (  86 expanded)
%              Number of leaves         :   15 (  59 expanded)
%              Depth                    :   19
%              Number of atoms          :  324 ( 934 expanded)
%              Number of equality atoms :  149 ( 293 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f26,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f25])).

fof(f32,plain,
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

fof(f33,plain,
    ( k1_funct_1(sK4,sK3) != sK2
    & r2_hidden(sK3,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))
    & v1_funct_2(sK4,sK1,k1_tarski(sK2))
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f26,f32])).

fof(f57,plain,(
    r2_hidden(sK3,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f12,axiom,(
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

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f12])).

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
    inference(flattening,[],[f23])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f55,plain,(
    v1_funct_2(sK4,sK1,k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f59,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f65,plain,(
    v1_funct_2(sK4,sK1,k1_enumset1(sK2,sK2,sK2)) ),
    inference(definition_unfolding,[],[f55,f59])).

fof(f56,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) ),
    inference(cnf_transformation,[],[f33])).

fof(f64,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_enumset1(sK2,sK2,sK2)))) ),
    inference(definition_unfolding,[],[f56,f59])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
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

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f36,f59])).

fof(f66,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_enumset1(X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f62])).

fof(f67,plain,(
    ! [X3] : r2_hidden(X3,k1_enumset1(X3,X3,X3)) ),
    inference(equality_resolution,[],[f66])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f54,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f35,f59])).

fof(f68,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_enumset1(X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f63])).

fof(f58,plain,(
    k1_funct_1(sK4,sK3) != sK2 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_19,negated_conjecture,
    ( r2_hidden(sK3,sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_767,plain,
    ( r2_hidden(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_21,negated_conjecture,
    ( v1_funct_2(sK4,sK1,k1_enumset1(sK2,sK2,sK2)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_346,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_enumset1(sK2,sK2,sK2) != X2
    | sK1 != X1
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_21])).

cnf(c_347,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_enumset1(sK2,sK2,sK2))))
    | k1_relset_1(sK1,k1_enumset1(sK2,sK2,sK2),sK4) = sK1
    | k1_xboole_0 = k1_enumset1(sK2,sK2,sK2) ),
    inference(unflattening,[status(thm)],[c_346])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_enumset1(sK2,sK2,sK2)))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_349,plain,
    ( k1_relset_1(sK1,k1_enumset1(sK2,sK2,sK2),sK4) = sK1
    | k1_xboole_0 = k1_enumset1(sK2,sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_347,c_20])).

cnf(c_766,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_enumset1(sK2,sK2,sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_769,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1275,plain,
    ( k1_relset_1(sK1,k1_enumset1(sK2,sK2,sK2),sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_766,c_769])).

cnf(c_1341,plain,
    ( k1_enumset1(sK2,sK2,sK2) = k1_xboole_0
    | k1_relat_1(sK4) = sK1 ),
    inference(superposition,[status(thm)],[c_349,c_1275])).

cnf(c_3,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_773,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1345,plain,
    ( k1_relat_1(sK4) = sK1
    | r2_hidden(sK2,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1341,c_773])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_252,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_7])).

cnf(c_253,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_252])).

cnf(c_765,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_253])).

cnf(c_1624,plain,
    ( k1_relat_1(sK4) = sK1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1345,c_765])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_263,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_22])).

cnf(c_264,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_263])).

cnf(c_282,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(sK4))
    | r2_hidden(k1_funct_1(sK4,X3),k2_relat_1(sK4))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_264])).

cnf(c_283,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r2_hidden(X2,k1_relat_1(sK4))
    | r2_hidden(k1_funct_1(sK4,X2),k2_relat_1(sK4)) ),
    inference(unflattening,[status(thm)],[c_282])).

cnf(c_468,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_283])).

cnf(c_764,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_468])).

cnf(c_25,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_enumset1(sK2,sK2,sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_470,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_283])).

cnf(c_496,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_470])).

cnf(c_500,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_468])).

cnf(c_469,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_283])).

cnf(c_886,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_enumset1(sK2,sK2,sK2))))
    | ~ sP1_iProver_split ),
    inference(instantiation,[status(thm)],[c_469])).

cnf(c_887,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_enumset1(sK2,sK2,sK2)))) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_886])).

cnf(c_1039,plain,
    ( r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_764,c_25,c_496,c_500,c_887])).

cnf(c_1040,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top ),
    inference(renaming,[status(thm)],[c_1039])).

cnf(c_1626,plain,
    ( r2_hidden(X0,sK1) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1624,c_1040])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_768,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1239,plain,
    ( k2_relset_1(sK1,k1_enumset1(sK2,sK2,sK2),sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_766,c_768])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_770,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1699,plain,
    ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_enumset1(sK2,sK2,sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1239,c_770])).

cnf(c_2046,plain,
    ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1699,c_25])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_771,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2052,plain,
    ( r2_hidden(X0,k1_enumset1(sK2,sK2,sK2)) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2046,c_771])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_772,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_enumset1(X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2274,plain,
    ( sK2 = X0
    | r2_hidden(X0,k2_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2052,c_772])).

cnf(c_2320,plain,
    ( k1_funct_1(sK4,X0) = sK2
    | r2_hidden(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1626,c_2274])).

cnf(c_2339,plain,
    ( k1_funct_1(sK4,sK3) = sK2 ),
    inference(superposition,[status(thm)],[c_767,c_2320])).

cnf(c_18,negated_conjecture,
    ( k1_funct_1(sK4,sK3) != sK2 ),
    inference(cnf_transformation,[],[f58])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2339,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:40:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 2.99/1.04  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.04  
% 2.99/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.99/1.04  
% 2.99/1.04  ------  iProver source info
% 2.99/1.04  
% 2.99/1.04  git: date: 2020-06-30 10:37:57 +0100
% 2.99/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.99/1.04  git: non_committed_changes: false
% 2.99/1.04  git: last_make_outside_of_git: false
% 2.99/1.04  
% 2.99/1.04  ------ 
% 2.99/1.04  
% 2.99/1.04  ------ Input Options
% 2.99/1.04  
% 2.99/1.04  --out_options                           all
% 2.99/1.04  --tptp_safe_out                         true
% 2.99/1.04  --problem_path                          ""
% 2.99/1.04  --include_path                          ""
% 2.99/1.04  --clausifier                            res/vclausify_rel
% 2.99/1.04  --clausifier_options                    --mode clausify
% 2.99/1.04  --stdin                                 false
% 2.99/1.04  --stats_out                             all
% 2.99/1.04  
% 2.99/1.04  ------ General Options
% 2.99/1.04  
% 2.99/1.04  --fof                                   false
% 2.99/1.04  --time_out_real                         305.
% 2.99/1.04  --time_out_virtual                      -1.
% 2.99/1.04  --symbol_type_check                     false
% 2.99/1.04  --clausify_out                          false
% 2.99/1.04  --sig_cnt_out                           false
% 2.99/1.04  --trig_cnt_out                          false
% 2.99/1.04  --trig_cnt_out_tolerance                1.
% 2.99/1.04  --trig_cnt_out_sk_spl                   false
% 2.99/1.04  --abstr_cl_out                          false
% 2.99/1.04  
% 2.99/1.04  ------ Global Options
% 2.99/1.04  
% 2.99/1.04  --schedule                              default
% 2.99/1.04  --add_important_lit                     false
% 2.99/1.04  --prop_solver_per_cl                    1000
% 2.99/1.04  --min_unsat_core                        false
% 2.99/1.04  --soft_assumptions                      false
% 2.99/1.04  --soft_lemma_size                       3
% 2.99/1.04  --prop_impl_unit_size                   0
% 2.99/1.04  --prop_impl_unit                        []
% 2.99/1.04  --share_sel_clauses                     true
% 2.99/1.04  --reset_solvers                         false
% 2.99/1.04  --bc_imp_inh                            [conj_cone]
% 2.99/1.04  --conj_cone_tolerance                   3.
% 2.99/1.04  --extra_neg_conj                        none
% 2.99/1.04  --large_theory_mode                     true
% 2.99/1.04  --prolific_symb_bound                   200
% 2.99/1.04  --lt_threshold                          2000
% 2.99/1.04  --clause_weak_htbl                      true
% 2.99/1.04  --gc_record_bc_elim                     false
% 2.99/1.04  
% 2.99/1.04  ------ Preprocessing Options
% 2.99/1.04  
% 2.99/1.04  --preprocessing_flag                    true
% 2.99/1.04  --time_out_prep_mult                    0.1
% 2.99/1.04  --splitting_mode                        input
% 2.99/1.04  --splitting_grd                         true
% 2.99/1.04  --splitting_cvd                         false
% 2.99/1.04  --splitting_cvd_svl                     false
% 2.99/1.04  --splitting_nvd                         32
% 2.99/1.04  --sub_typing                            true
% 2.99/1.04  --prep_gs_sim                           true
% 2.99/1.04  --prep_unflatten                        true
% 2.99/1.04  --prep_res_sim                          true
% 2.99/1.04  --prep_upred                            true
% 2.99/1.04  --prep_sem_filter                       exhaustive
% 2.99/1.04  --prep_sem_filter_out                   false
% 2.99/1.04  --pred_elim                             true
% 2.99/1.04  --res_sim_input                         true
% 2.99/1.04  --eq_ax_congr_red                       true
% 2.99/1.04  --pure_diseq_elim                       true
% 2.99/1.04  --brand_transform                       false
% 2.99/1.04  --non_eq_to_eq                          false
% 2.99/1.04  --prep_def_merge                        true
% 2.99/1.04  --prep_def_merge_prop_impl              false
% 2.99/1.04  --prep_def_merge_mbd                    true
% 2.99/1.04  --prep_def_merge_tr_red                 false
% 2.99/1.04  --prep_def_merge_tr_cl                  false
% 2.99/1.04  --smt_preprocessing                     true
% 2.99/1.04  --smt_ac_axioms                         fast
% 2.99/1.04  --preprocessed_out                      false
% 2.99/1.04  --preprocessed_stats                    false
% 2.99/1.04  
% 2.99/1.04  ------ Abstraction refinement Options
% 2.99/1.04  
% 2.99/1.04  --abstr_ref                             []
% 2.99/1.04  --abstr_ref_prep                        false
% 2.99/1.04  --abstr_ref_until_sat                   false
% 2.99/1.04  --abstr_ref_sig_restrict                funpre
% 2.99/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 2.99/1.04  --abstr_ref_under                       []
% 2.99/1.04  
% 2.99/1.04  ------ SAT Options
% 2.99/1.04  
% 2.99/1.04  --sat_mode                              false
% 2.99/1.04  --sat_fm_restart_options                ""
% 2.99/1.04  --sat_gr_def                            false
% 2.99/1.04  --sat_epr_types                         true
% 2.99/1.04  --sat_non_cyclic_types                  false
% 2.99/1.04  --sat_finite_models                     false
% 2.99/1.04  --sat_fm_lemmas                         false
% 2.99/1.04  --sat_fm_prep                           false
% 2.99/1.04  --sat_fm_uc_incr                        true
% 2.99/1.04  --sat_out_model                         small
% 2.99/1.04  --sat_out_clauses                       false
% 2.99/1.04  
% 2.99/1.04  ------ QBF Options
% 2.99/1.04  
% 2.99/1.04  --qbf_mode                              false
% 2.99/1.04  --qbf_elim_univ                         false
% 2.99/1.04  --qbf_dom_inst                          none
% 2.99/1.04  --qbf_dom_pre_inst                      false
% 2.99/1.04  --qbf_sk_in                             false
% 2.99/1.04  --qbf_pred_elim                         true
% 2.99/1.04  --qbf_split                             512
% 2.99/1.04  
% 2.99/1.04  ------ BMC1 Options
% 2.99/1.04  
% 2.99/1.04  --bmc1_incremental                      false
% 2.99/1.04  --bmc1_axioms                           reachable_all
% 2.99/1.04  --bmc1_min_bound                        0
% 2.99/1.04  --bmc1_max_bound                        -1
% 2.99/1.04  --bmc1_max_bound_default                -1
% 2.99/1.04  --bmc1_symbol_reachability              true
% 2.99/1.04  --bmc1_property_lemmas                  false
% 2.99/1.04  --bmc1_k_induction                      false
% 2.99/1.04  --bmc1_non_equiv_states                 false
% 2.99/1.04  --bmc1_deadlock                         false
% 2.99/1.04  --bmc1_ucm                              false
% 2.99/1.04  --bmc1_add_unsat_core                   none
% 2.99/1.04  --bmc1_unsat_core_children              false
% 2.99/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 2.99/1.04  --bmc1_out_stat                         full
% 2.99/1.04  --bmc1_ground_init                      false
% 2.99/1.04  --bmc1_pre_inst_next_state              false
% 2.99/1.04  --bmc1_pre_inst_state                   false
% 2.99/1.04  --bmc1_pre_inst_reach_state             false
% 2.99/1.04  --bmc1_out_unsat_core                   false
% 2.99/1.04  --bmc1_aig_witness_out                  false
% 2.99/1.04  --bmc1_verbose                          false
% 2.99/1.04  --bmc1_dump_clauses_tptp                false
% 2.99/1.04  --bmc1_dump_unsat_core_tptp             false
% 2.99/1.04  --bmc1_dump_file                        -
% 2.99/1.04  --bmc1_ucm_expand_uc_limit              128
% 2.99/1.04  --bmc1_ucm_n_expand_iterations          6
% 2.99/1.04  --bmc1_ucm_extend_mode                  1
% 2.99/1.04  --bmc1_ucm_init_mode                    2
% 2.99/1.04  --bmc1_ucm_cone_mode                    none
% 2.99/1.04  --bmc1_ucm_reduced_relation_type        0
% 2.99/1.04  --bmc1_ucm_relax_model                  4
% 2.99/1.04  --bmc1_ucm_full_tr_after_sat            true
% 2.99/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 2.99/1.04  --bmc1_ucm_layered_model                none
% 2.99/1.04  --bmc1_ucm_max_lemma_size               10
% 2.99/1.04  
% 2.99/1.04  ------ AIG Options
% 2.99/1.04  
% 2.99/1.04  --aig_mode                              false
% 2.99/1.04  
% 2.99/1.04  ------ Instantiation Options
% 2.99/1.04  
% 2.99/1.04  --instantiation_flag                    true
% 2.99/1.04  --inst_sos_flag                         false
% 2.99/1.04  --inst_sos_phase                        true
% 2.99/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.99/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.99/1.04  --inst_lit_sel_side                     num_symb
% 2.99/1.04  --inst_solver_per_active                1400
% 2.99/1.04  --inst_solver_calls_frac                1.
% 2.99/1.04  --inst_passive_queue_type               priority_queues
% 2.99/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.99/1.04  --inst_passive_queues_freq              [25;2]
% 2.99/1.04  --inst_dismatching                      true
% 2.99/1.04  --inst_eager_unprocessed_to_passive     true
% 2.99/1.04  --inst_prop_sim_given                   true
% 2.99/1.04  --inst_prop_sim_new                     false
% 2.99/1.04  --inst_subs_new                         false
% 2.99/1.04  --inst_eq_res_simp                      false
% 2.99/1.04  --inst_subs_given                       false
% 2.99/1.04  --inst_orphan_elimination               true
% 2.99/1.04  --inst_learning_loop_flag               true
% 2.99/1.04  --inst_learning_start                   3000
% 2.99/1.04  --inst_learning_factor                  2
% 2.99/1.04  --inst_start_prop_sim_after_learn       3
% 2.99/1.04  --inst_sel_renew                        solver
% 2.99/1.04  --inst_lit_activity_flag                true
% 2.99/1.04  --inst_restr_to_given                   false
% 2.99/1.04  --inst_activity_threshold               500
% 2.99/1.04  --inst_out_proof                        true
% 2.99/1.04  
% 2.99/1.04  ------ Resolution Options
% 2.99/1.04  
% 2.99/1.04  --resolution_flag                       true
% 2.99/1.04  --res_lit_sel                           adaptive
% 2.99/1.04  --res_lit_sel_side                      none
% 2.99/1.04  --res_ordering                          kbo
% 2.99/1.04  --res_to_prop_solver                    active
% 2.99/1.04  --res_prop_simpl_new                    false
% 2.99/1.04  --res_prop_simpl_given                  true
% 2.99/1.04  --res_passive_queue_type                priority_queues
% 2.99/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.99/1.04  --res_passive_queues_freq               [15;5]
% 2.99/1.04  --res_forward_subs                      full
% 2.99/1.04  --res_backward_subs                     full
% 2.99/1.04  --res_forward_subs_resolution           true
% 2.99/1.04  --res_backward_subs_resolution          true
% 2.99/1.04  --res_orphan_elimination                true
% 2.99/1.04  --res_time_limit                        2.
% 2.99/1.04  --res_out_proof                         true
% 2.99/1.04  
% 2.99/1.04  ------ Superposition Options
% 2.99/1.04  
% 2.99/1.04  --superposition_flag                    true
% 2.99/1.04  --sup_passive_queue_type                priority_queues
% 2.99/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.99/1.04  --sup_passive_queues_freq               [8;1;4]
% 2.99/1.04  --demod_completeness_check              fast
% 2.99/1.04  --demod_use_ground                      true
% 2.99/1.04  --sup_to_prop_solver                    passive
% 2.99/1.04  --sup_prop_simpl_new                    true
% 2.99/1.04  --sup_prop_simpl_given                  true
% 2.99/1.04  --sup_fun_splitting                     false
% 2.99/1.04  --sup_smt_interval                      50000
% 2.99/1.04  
% 2.99/1.04  ------ Superposition Simplification Setup
% 2.99/1.04  
% 2.99/1.04  --sup_indices_passive                   []
% 2.99/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 2.99/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/1.04  --sup_full_bw                           [BwDemod]
% 2.99/1.04  --sup_immed_triv                        [TrivRules]
% 2.99/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.99/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/1.04  --sup_immed_bw_main                     []
% 2.99/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.99/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 2.99/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.99/1.04  
% 2.99/1.04  ------ Combination Options
% 2.99/1.04  
% 2.99/1.04  --comb_res_mult                         3
% 2.99/1.04  --comb_sup_mult                         2
% 2.99/1.04  --comb_inst_mult                        10
% 2.99/1.04  
% 2.99/1.04  ------ Debug Options
% 2.99/1.04  
% 2.99/1.04  --dbg_backtrace                         false
% 2.99/1.04  --dbg_dump_prop_clauses                 false
% 2.99/1.04  --dbg_dump_prop_clauses_file            -
% 2.99/1.04  --dbg_out_stat                          false
% 2.99/1.04  ------ Parsing...
% 2.99/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.99/1.04  
% 2.99/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.99/1.04  
% 2.99/1.04  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.99/1.04  
% 2.99/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.99/1.04  ------ Proving...
% 2.99/1.04  ------ Problem Properties 
% 2.99/1.04  
% 2.99/1.04  
% 2.99/1.04  clauses                                 18
% 2.99/1.04  conjectures                             3
% 2.99/1.04  EPR                                     3
% 2.99/1.04  Horn                                    14
% 2.99/1.04  unary                                   5
% 2.99/1.04  binary                                  7
% 2.99/1.04  lits                                    38
% 2.99/1.04  lits eq                                 15
% 2.99/1.04  fd_pure                                 0
% 2.99/1.04  fd_pseudo                               0
% 2.99/1.04  fd_cond                                 0
% 2.99/1.04  fd_pseudo_cond                          2
% 2.99/1.04  AC symbols                              0
% 2.99/1.04  
% 2.99/1.04  ------ Schedule dynamic 5 is on 
% 2.99/1.04  
% 2.99/1.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.99/1.04  
% 2.99/1.04  
% 2.99/1.04  ------ 
% 2.99/1.04  Current options:
% 2.99/1.04  ------ 
% 2.99/1.04  
% 2.99/1.04  ------ Input Options
% 2.99/1.04  
% 2.99/1.04  --out_options                           all
% 2.99/1.04  --tptp_safe_out                         true
% 2.99/1.04  --problem_path                          ""
% 2.99/1.04  --include_path                          ""
% 2.99/1.04  --clausifier                            res/vclausify_rel
% 2.99/1.04  --clausifier_options                    --mode clausify
% 2.99/1.04  --stdin                                 false
% 2.99/1.04  --stats_out                             all
% 2.99/1.04  
% 2.99/1.04  ------ General Options
% 2.99/1.04  
% 2.99/1.04  --fof                                   false
% 2.99/1.04  --time_out_real                         305.
% 2.99/1.04  --time_out_virtual                      -1.
% 2.99/1.04  --symbol_type_check                     false
% 2.99/1.04  --clausify_out                          false
% 2.99/1.04  --sig_cnt_out                           false
% 2.99/1.04  --trig_cnt_out                          false
% 2.99/1.04  --trig_cnt_out_tolerance                1.
% 2.99/1.04  --trig_cnt_out_sk_spl                   false
% 2.99/1.04  --abstr_cl_out                          false
% 2.99/1.04  
% 2.99/1.04  ------ Global Options
% 2.99/1.04  
% 2.99/1.04  --schedule                              default
% 2.99/1.04  --add_important_lit                     false
% 2.99/1.04  --prop_solver_per_cl                    1000
% 2.99/1.04  --min_unsat_core                        false
% 2.99/1.04  --soft_assumptions                      false
% 2.99/1.04  --soft_lemma_size                       3
% 2.99/1.04  --prop_impl_unit_size                   0
% 2.99/1.04  --prop_impl_unit                        []
% 2.99/1.04  --share_sel_clauses                     true
% 2.99/1.04  --reset_solvers                         false
% 2.99/1.04  --bc_imp_inh                            [conj_cone]
% 2.99/1.04  --conj_cone_tolerance                   3.
% 2.99/1.04  --extra_neg_conj                        none
% 2.99/1.04  --large_theory_mode                     true
% 2.99/1.04  --prolific_symb_bound                   200
% 2.99/1.04  --lt_threshold                          2000
% 2.99/1.04  --clause_weak_htbl                      true
% 2.99/1.04  --gc_record_bc_elim                     false
% 2.99/1.04  
% 2.99/1.04  ------ Preprocessing Options
% 2.99/1.04  
% 2.99/1.04  --preprocessing_flag                    true
% 2.99/1.04  --time_out_prep_mult                    0.1
% 2.99/1.04  --splitting_mode                        input
% 2.99/1.04  --splitting_grd                         true
% 2.99/1.04  --splitting_cvd                         false
% 2.99/1.04  --splitting_cvd_svl                     false
% 2.99/1.04  --splitting_nvd                         32
% 2.99/1.04  --sub_typing                            true
% 2.99/1.04  --prep_gs_sim                           true
% 2.99/1.04  --prep_unflatten                        true
% 2.99/1.04  --prep_res_sim                          true
% 2.99/1.04  --prep_upred                            true
% 2.99/1.04  --prep_sem_filter                       exhaustive
% 2.99/1.04  --prep_sem_filter_out                   false
% 2.99/1.04  --pred_elim                             true
% 2.99/1.04  --res_sim_input                         true
% 2.99/1.04  --eq_ax_congr_red                       true
% 2.99/1.04  --pure_diseq_elim                       true
% 2.99/1.04  --brand_transform                       false
% 2.99/1.04  --non_eq_to_eq                          false
% 2.99/1.04  --prep_def_merge                        true
% 2.99/1.04  --prep_def_merge_prop_impl              false
% 2.99/1.04  --prep_def_merge_mbd                    true
% 2.99/1.04  --prep_def_merge_tr_red                 false
% 2.99/1.04  --prep_def_merge_tr_cl                  false
% 2.99/1.04  --smt_preprocessing                     true
% 2.99/1.04  --smt_ac_axioms                         fast
% 2.99/1.04  --preprocessed_out                      false
% 2.99/1.04  --preprocessed_stats                    false
% 2.99/1.04  
% 2.99/1.04  ------ Abstraction refinement Options
% 2.99/1.04  
% 2.99/1.04  --abstr_ref                             []
% 2.99/1.04  --abstr_ref_prep                        false
% 2.99/1.04  --abstr_ref_until_sat                   false
% 2.99/1.04  --abstr_ref_sig_restrict                funpre
% 2.99/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 2.99/1.04  --abstr_ref_under                       []
% 2.99/1.04  
% 2.99/1.04  ------ SAT Options
% 2.99/1.04  
% 2.99/1.04  --sat_mode                              false
% 2.99/1.04  --sat_fm_restart_options                ""
% 2.99/1.04  --sat_gr_def                            false
% 2.99/1.04  --sat_epr_types                         true
% 2.99/1.04  --sat_non_cyclic_types                  false
% 2.99/1.04  --sat_finite_models                     false
% 2.99/1.04  --sat_fm_lemmas                         false
% 2.99/1.04  --sat_fm_prep                           false
% 2.99/1.04  --sat_fm_uc_incr                        true
% 2.99/1.04  --sat_out_model                         small
% 2.99/1.04  --sat_out_clauses                       false
% 2.99/1.04  
% 2.99/1.04  ------ QBF Options
% 2.99/1.04  
% 2.99/1.04  --qbf_mode                              false
% 2.99/1.04  --qbf_elim_univ                         false
% 2.99/1.04  --qbf_dom_inst                          none
% 2.99/1.04  --qbf_dom_pre_inst                      false
% 2.99/1.04  --qbf_sk_in                             false
% 2.99/1.04  --qbf_pred_elim                         true
% 2.99/1.04  --qbf_split                             512
% 2.99/1.04  
% 2.99/1.04  ------ BMC1 Options
% 2.99/1.04  
% 2.99/1.04  --bmc1_incremental                      false
% 2.99/1.04  --bmc1_axioms                           reachable_all
% 2.99/1.04  --bmc1_min_bound                        0
% 2.99/1.04  --bmc1_max_bound                        -1
% 2.99/1.04  --bmc1_max_bound_default                -1
% 2.99/1.04  --bmc1_symbol_reachability              true
% 2.99/1.04  --bmc1_property_lemmas                  false
% 2.99/1.04  --bmc1_k_induction                      false
% 2.99/1.04  --bmc1_non_equiv_states                 false
% 2.99/1.04  --bmc1_deadlock                         false
% 2.99/1.04  --bmc1_ucm                              false
% 2.99/1.04  --bmc1_add_unsat_core                   none
% 2.99/1.04  --bmc1_unsat_core_children              false
% 2.99/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 2.99/1.04  --bmc1_out_stat                         full
% 2.99/1.04  --bmc1_ground_init                      false
% 2.99/1.04  --bmc1_pre_inst_next_state              false
% 2.99/1.04  --bmc1_pre_inst_state                   false
% 2.99/1.04  --bmc1_pre_inst_reach_state             false
% 2.99/1.04  --bmc1_out_unsat_core                   false
% 2.99/1.04  --bmc1_aig_witness_out                  false
% 2.99/1.04  --bmc1_verbose                          false
% 2.99/1.04  --bmc1_dump_clauses_tptp                false
% 2.99/1.04  --bmc1_dump_unsat_core_tptp             false
% 2.99/1.04  --bmc1_dump_file                        -
% 2.99/1.04  --bmc1_ucm_expand_uc_limit              128
% 2.99/1.04  --bmc1_ucm_n_expand_iterations          6
% 2.99/1.04  --bmc1_ucm_extend_mode                  1
% 2.99/1.04  --bmc1_ucm_init_mode                    2
% 2.99/1.04  --bmc1_ucm_cone_mode                    none
% 2.99/1.04  --bmc1_ucm_reduced_relation_type        0
% 2.99/1.04  --bmc1_ucm_relax_model                  4
% 2.99/1.04  --bmc1_ucm_full_tr_after_sat            true
% 2.99/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 2.99/1.04  --bmc1_ucm_layered_model                none
% 2.99/1.04  --bmc1_ucm_max_lemma_size               10
% 2.99/1.04  
% 2.99/1.04  ------ AIG Options
% 2.99/1.04  
% 2.99/1.04  --aig_mode                              false
% 2.99/1.04  
% 2.99/1.04  ------ Instantiation Options
% 2.99/1.04  
% 2.99/1.04  --instantiation_flag                    true
% 2.99/1.04  --inst_sos_flag                         false
% 2.99/1.04  --inst_sos_phase                        true
% 2.99/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.99/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.99/1.04  --inst_lit_sel_side                     none
% 2.99/1.04  --inst_solver_per_active                1400
% 2.99/1.04  --inst_solver_calls_frac                1.
% 2.99/1.04  --inst_passive_queue_type               priority_queues
% 2.99/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.99/1.04  --inst_passive_queues_freq              [25;2]
% 2.99/1.04  --inst_dismatching                      true
% 2.99/1.04  --inst_eager_unprocessed_to_passive     true
% 2.99/1.04  --inst_prop_sim_given                   true
% 2.99/1.04  --inst_prop_sim_new                     false
% 2.99/1.04  --inst_subs_new                         false
% 2.99/1.04  --inst_eq_res_simp                      false
% 2.99/1.04  --inst_subs_given                       false
% 2.99/1.04  --inst_orphan_elimination               true
% 2.99/1.04  --inst_learning_loop_flag               true
% 2.99/1.04  --inst_learning_start                   3000
% 2.99/1.04  --inst_learning_factor                  2
% 2.99/1.04  --inst_start_prop_sim_after_learn       3
% 2.99/1.04  --inst_sel_renew                        solver
% 2.99/1.04  --inst_lit_activity_flag                true
% 2.99/1.04  --inst_restr_to_given                   false
% 2.99/1.04  --inst_activity_threshold               500
% 2.99/1.04  --inst_out_proof                        true
% 2.99/1.04  
% 2.99/1.04  ------ Resolution Options
% 2.99/1.04  
% 2.99/1.04  --resolution_flag                       false
% 2.99/1.04  --res_lit_sel                           adaptive
% 2.99/1.04  --res_lit_sel_side                      none
% 2.99/1.04  --res_ordering                          kbo
% 2.99/1.04  --res_to_prop_solver                    active
% 2.99/1.04  --res_prop_simpl_new                    false
% 2.99/1.04  --res_prop_simpl_given                  true
% 2.99/1.04  --res_passive_queue_type                priority_queues
% 2.99/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.99/1.04  --res_passive_queues_freq               [15;5]
% 2.99/1.04  --res_forward_subs                      full
% 2.99/1.04  --res_backward_subs                     full
% 2.99/1.04  --res_forward_subs_resolution           true
% 2.99/1.04  --res_backward_subs_resolution          true
% 2.99/1.04  --res_orphan_elimination                true
% 2.99/1.04  --res_time_limit                        2.
% 2.99/1.04  --res_out_proof                         true
% 2.99/1.04  
% 2.99/1.04  ------ Superposition Options
% 2.99/1.04  
% 2.99/1.04  --superposition_flag                    true
% 2.99/1.04  --sup_passive_queue_type                priority_queues
% 2.99/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.99/1.04  --sup_passive_queues_freq               [8;1;4]
% 2.99/1.04  --demod_completeness_check              fast
% 2.99/1.04  --demod_use_ground                      true
% 2.99/1.04  --sup_to_prop_solver                    passive
% 2.99/1.04  --sup_prop_simpl_new                    true
% 2.99/1.04  --sup_prop_simpl_given                  true
% 2.99/1.04  --sup_fun_splitting                     false
% 2.99/1.04  --sup_smt_interval                      50000
% 2.99/1.04  
% 2.99/1.04  ------ Superposition Simplification Setup
% 2.99/1.04  
% 2.99/1.04  --sup_indices_passive                   []
% 2.99/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 2.99/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/1.04  --sup_full_bw                           [BwDemod]
% 2.99/1.04  --sup_immed_triv                        [TrivRules]
% 2.99/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.99/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/1.04  --sup_immed_bw_main                     []
% 2.99/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.99/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 2.99/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.99/1.04  
% 2.99/1.04  ------ Combination Options
% 2.99/1.04  
% 2.99/1.04  --comb_res_mult                         3
% 2.99/1.04  --comb_sup_mult                         2
% 2.99/1.04  --comb_inst_mult                        10
% 2.99/1.04  
% 2.99/1.04  ------ Debug Options
% 2.99/1.04  
% 2.99/1.04  --dbg_backtrace                         false
% 2.99/1.04  --dbg_dump_prop_clauses                 false
% 2.99/1.04  --dbg_dump_prop_clauses_file            -
% 2.99/1.04  --dbg_out_stat                          false
% 2.99/1.04  
% 2.99/1.04  
% 2.99/1.04  
% 2.99/1.04  
% 2.99/1.04  ------ Proving...
% 2.99/1.04  
% 2.99/1.04  
% 2.99/1.04  % SZS status Theorem for theBenchmark.p
% 2.99/1.04  
% 2.99/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 2.99/1.04  
% 2.99/1.04  fof(f13,conjecture,(
% 2.99/1.04    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 2.99/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/1.04  
% 2.99/1.04  fof(f14,negated_conjecture,(
% 2.99/1.04    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 2.99/1.04    inference(negated_conjecture,[],[f13])).
% 2.99/1.04  
% 2.99/1.04  fof(f25,plain,(
% 2.99/1.04    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 2.99/1.04    inference(ennf_transformation,[],[f14])).
% 2.99/1.04  
% 2.99/1.04  fof(f26,plain,(
% 2.99/1.04    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 2.99/1.04    inference(flattening,[],[f25])).
% 2.99/1.04  
% 2.99/1.04  fof(f32,plain,(
% 2.99/1.04    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (k1_funct_1(sK4,sK3) != sK2 & r2_hidden(sK3,sK1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) & v1_funct_2(sK4,sK1,k1_tarski(sK2)) & v1_funct_1(sK4))),
% 2.99/1.04    introduced(choice_axiom,[])).
% 2.99/1.04  
% 2.99/1.04  fof(f33,plain,(
% 2.99/1.04    k1_funct_1(sK4,sK3) != sK2 & r2_hidden(sK3,sK1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) & v1_funct_2(sK4,sK1,k1_tarski(sK2)) & v1_funct_1(sK4)),
% 2.99/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f26,f32])).
% 2.99/1.04  
% 2.99/1.04  fof(f57,plain,(
% 2.99/1.04    r2_hidden(sK3,sK1)),
% 2.99/1.04    inference(cnf_transformation,[],[f33])).
% 2.99/1.04  
% 2.99/1.04  fof(f12,axiom,(
% 2.99/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.99/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/1.04  
% 2.99/1.04  fof(f23,plain,(
% 2.99/1.04    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.99/1.04    inference(ennf_transformation,[],[f12])).
% 2.99/1.04  
% 2.99/1.04  fof(f24,plain,(
% 2.99/1.04    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.99/1.04    inference(flattening,[],[f23])).
% 2.99/1.04  
% 2.99/1.04  fof(f31,plain,(
% 2.99/1.04    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.99/1.04    inference(nnf_transformation,[],[f24])).
% 2.99/1.04  
% 2.99/1.04  fof(f48,plain,(
% 2.99/1.04    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.99/1.04    inference(cnf_transformation,[],[f31])).
% 2.99/1.04  
% 2.99/1.04  fof(f55,plain,(
% 2.99/1.04    v1_funct_2(sK4,sK1,k1_tarski(sK2))),
% 2.99/1.04    inference(cnf_transformation,[],[f33])).
% 2.99/1.04  
% 2.99/1.04  fof(f3,axiom,(
% 2.99/1.04    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 2.99/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/1.04  
% 2.99/1.04  fof(f39,plain,(
% 2.99/1.04    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 2.99/1.04    inference(cnf_transformation,[],[f3])).
% 2.99/1.04  
% 2.99/1.04  fof(f4,axiom,(
% 2.99/1.04    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.99/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/1.04  
% 2.99/1.04  fof(f40,plain,(
% 2.99/1.04    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.99/1.04    inference(cnf_transformation,[],[f4])).
% 2.99/1.04  
% 2.99/1.04  fof(f59,plain,(
% 2.99/1.04    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 2.99/1.04    inference(definition_unfolding,[],[f39,f40])).
% 2.99/1.04  
% 2.99/1.04  fof(f65,plain,(
% 2.99/1.04    v1_funct_2(sK4,sK1,k1_enumset1(sK2,sK2,sK2))),
% 2.99/1.04    inference(definition_unfolding,[],[f55,f59])).
% 2.99/1.04  
% 2.99/1.04  fof(f56,plain,(
% 2.99/1.04    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))),
% 2.99/1.04    inference(cnf_transformation,[],[f33])).
% 2.99/1.04  
% 2.99/1.04  fof(f64,plain,(
% 2.99/1.04    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_enumset1(sK2,sK2,sK2))))),
% 2.99/1.04    inference(definition_unfolding,[],[f56,f59])).
% 2.99/1.04  
% 2.99/1.04  fof(f10,axiom,(
% 2.99/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.99/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/1.04  
% 2.99/1.04  fof(f21,plain,(
% 2.99/1.04    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.99/1.04    inference(ennf_transformation,[],[f10])).
% 2.99/1.04  
% 2.99/1.04  fof(f46,plain,(
% 2.99/1.04    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.99/1.04    inference(cnf_transformation,[],[f21])).
% 2.99/1.04  
% 2.99/1.04  fof(f2,axiom,(
% 2.99/1.04    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.99/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/1.04  
% 2.99/1.04  fof(f27,plain,(
% 2.99/1.04    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.99/1.04    inference(nnf_transformation,[],[f2])).
% 2.99/1.04  
% 2.99/1.04  fof(f28,plain,(
% 2.99/1.04    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.99/1.04    inference(rectify,[],[f27])).
% 2.99/1.04  
% 2.99/1.04  fof(f29,plain,(
% 2.99/1.04    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1))))),
% 2.99/1.04    introduced(choice_axiom,[])).
% 2.99/1.04  
% 2.99/1.04  fof(f30,plain,(
% 2.99/1.04    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.99/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 2.99/1.04  
% 2.99/1.04  fof(f36,plain,(
% 2.99/1.04    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 2.99/1.04    inference(cnf_transformation,[],[f30])).
% 2.99/1.04  
% 2.99/1.04  fof(f62,plain,(
% 2.99/1.04    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_enumset1(X0,X0,X0) != X1) )),
% 2.99/1.04    inference(definition_unfolding,[],[f36,f59])).
% 2.99/1.04  
% 2.99/1.04  fof(f66,plain,(
% 2.99/1.04    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_enumset1(X3,X3,X3) != X1) )),
% 2.99/1.04    inference(equality_resolution,[],[f62])).
% 2.99/1.04  
% 2.99/1.04  fof(f67,plain,(
% 2.99/1.04    ( ! [X3] : (r2_hidden(X3,k1_enumset1(X3,X3,X3))) )),
% 2.99/1.04    inference(equality_resolution,[],[f66])).
% 2.99/1.04  
% 2.99/1.04  fof(f1,axiom,(
% 2.99/1.04    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.99/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/1.04  
% 2.99/1.04  fof(f34,plain,(
% 2.99/1.04    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.99/1.04    inference(cnf_transformation,[],[f1])).
% 2.99/1.04  
% 2.99/1.04  fof(f7,axiom,(
% 2.99/1.04    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.99/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/1.04  
% 2.99/1.04  fof(f18,plain,(
% 2.99/1.04    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.99/1.04    inference(ennf_transformation,[],[f7])).
% 2.99/1.04  
% 2.99/1.04  fof(f43,plain,(
% 2.99/1.04    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.99/1.04    inference(cnf_transformation,[],[f18])).
% 2.99/1.04  
% 2.99/1.04  fof(f8,axiom,(
% 2.99/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.99/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/1.04  
% 2.99/1.04  fof(f19,plain,(
% 2.99/1.04    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.99/1.04    inference(ennf_transformation,[],[f8])).
% 2.99/1.04  
% 2.99/1.04  fof(f44,plain,(
% 2.99/1.04    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.99/1.04    inference(cnf_transformation,[],[f19])).
% 2.99/1.04  
% 2.99/1.04  fof(f6,axiom,(
% 2.99/1.04    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 2.99/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/1.04  
% 2.99/1.04  fof(f16,plain,(
% 2.99/1.04    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.99/1.04    inference(ennf_transformation,[],[f6])).
% 2.99/1.04  
% 2.99/1.04  fof(f17,plain,(
% 2.99/1.04    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.99/1.04    inference(flattening,[],[f16])).
% 2.99/1.04  
% 2.99/1.04  fof(f42,plain,(
% 2.99/1.04    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.99/1.04    inference(cnf_transformation,[],[f17])).
% 2.99/1.04  
% 2.99/1.04  fof(f54,plain,(
% 2.99/1.04    v1_funct_1(sK4)),
% 2.99/1.04    inference(cnf_transformation,[],[f33])).
% 2.99/1.04  
% 2.99/1.04  fof(f11,axiom,(
% 2.99/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.99/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/1.04  
% 2.99/1.04  fof(f22,plain,(
% 2.99/1.04    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.99/1.04    inference(ennf_transformation,[],[f11])).
% 2.99/1.04  
% 2.99/1.04  fof(f47,plain,(
% 2.99/1.04    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.99/1.04    inference(cnf_transformation,[],[f22])).
% 2.99/1.04  
% 2.99/1.04  fof(f9,axiom,(
% 2.99/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 2.99/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/1.04  
% 2.99/1.04  fof(f20,plain,(
% 2.99/1.04    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.99/1.04    inference(ennf_transformation,[],[f9])).
% 2.99/1.04  
% 2.99/1.04  fof(f45,plain,(
% 2.99/1.04    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.99/1.04    inference(cnf_transformation,[],[f20])).
% 2.99/1.04  
% 2.99/1.04  fof(f5,axiom,(
% 2.99/1.04    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.99/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/1.04  
% 2.99/1.04  fof(f15,plain,(
% 2.99/1.04    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.99/1.04    inference(ennf_transformation,[],[f5])).
% 2.99/1.04  
% 2.99/1.04  fof(f41,plain,(
% 2.99/1.04    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.99/1.04    inference(cnf_transformation,[],[f15])).
% 2.99/1.04  
% 2.99/1.04  fof(f35,plain,(
% 2.99/1.04    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 2.99/1.04    inference(cnf_transformation,[],[f30])).
% 2.99/1.04  
% 2.99/1.04  fof(f63,plain,(
% 2.99/1.04    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_enumset1(X0,X0,X0) != X1) )),
% 2.99/1.04    inference(definition_unfolding,[],[f35,f59])).
% 2.99/1.04  
% 2.99/1.04  fof(f68,plain,(
% 2.99/1.04    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_enumset1(X0,X0,X0))) )),
% 2.99/1.04    inference(equality_resolution,[],[f63])).
% 2.99/1.04  
% 2.99/1.04  fof(f58,plain,(
% 2.99/1.04    k1_funct_1(sK4,sK3) != sK2),
% 2.99/1.04    inference(cnf_transformation,[],[f33])).
% 2.99/1.04  
% 2.99/1.04  cnf(c_19,negated_conjecture,
% 2.99/1.04      ( r2_hidden(sK3,sK1) ),
% 2.99/1.04      inference(cnf_transformation,[],[f57]) ).
% 2.99/1.04  
% 2.99/1.04  cnf(c_767,plain,
% 2.99/1.04      ( r2_hidden(sK3,sK1) = iProver_top ),
% 2.99/1.04      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.99/1.04  
% 2.99/1.04  cnf(c_17,plain,
% 2.99/1.04      ( ~ v1_funct_2(X0,X1,X2)
% 2.99/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.99/1.04      | k1_relset_1(X1,X2,X0) = X1
% 2.99/1.04      | k1_xboole_0 = X2 ),
% 2.99/1.04      inference(cnf_transformation,[],[f48]) ).
% 2.99/1.04  
% 2.99/1.04  cnf(c_21,negated_conjecture,
% 2.99/1.04      ( v1_funct_2(sK4,sK1,k1_enumset1(sK2,sK2,sK2)) ),
% 2.99/1.04      inference(cnf_transformation,[],[f65]) ).
% 2.99/1.04  
% 2.99/1.04  cnf(c_346,plain,
% 2.99/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.99/1.04      | k1_relset_1(X1,X2,X0) = X1
% 2.99/1.04      | k1_enumset1(sK2,sK2,sK2) != X2
% 2.99/1.04      | sK1 != X1
% 2.99/1.04      | sK4 != X0
% 2.99/1.04      | k1_xboole_0 = X2 ),
% 2.99/1.04      inference(resolution_lifted,[status(thm)],[c_17,c_21]) ).
% 2.99/1.04  
% 2.99/1.04  cnf(c_347,plain,
% 2.99/1.04      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_enumset1(sK2,sK2,sK2))))
% 2.99/1.04      | k1_relset_1(sK1,k1_enumset1(sK2,sK2,sK2),sK4) = sK1
% 2.99/1.04      | k1_xboole_0 = k1_enumset1(sK2,sK2,sK2) ),
% 2.99/1.04      inference(unflattening,[status(thm)],[c_346]) ).
% 2.99/1.04  
% 2.99/1.04  cnf(c_20,negated_conjecture,
% 2.99/1.04      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_enumset1(sK2,sK2,sK2)))) ),
% 2.99/1.04      inference(cnf_transformation,[],[f64]) ).
% 2.99/1.04  
% 2.99/1.04  cnf(c_349,plain,
% 2.99/1.04      ( k1_relset_1(sK1,k1_enumset1(sK2,sK2,sK2),sK4) = sK1
% 2.99/1.04      | k1_xboole_0 = k1_enumset1(sK2,sK2,sK2) ),
% 2.99/1.04      inference(global_propositional_subsumption,
% 2.99/1.04                [status(thm)],
% 2.99/1.04                [c_347,c_20]) ).
% 2.99/1.04  
% 2.99/1.04  cnf(c_766,plain,
% 2.99/1.04      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_enumset1(sK2,sK2,sK2)))) = iProver_top ),
% 2.99/1.04      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.99/1.04  
% 2.99/1.04  cnf(c_10,plain,
% 2.99/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.99/1.04      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.99/1.04      inference(cnf_transformation,[],[f46]) ).
% 2.99/1.04  
% 2.99/1.04  cnf(c_769,plain,
% 2.99/1.04      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.99/1.04      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.99/1.04      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.99/1.04  
% 2.99/1.04  cnf(c_1275,plain,
% 2.99/1.04      ( k1_relset_1(sK1,k1_enumset1(sK2,sK2,sK2),sK4) = k1_relat_1(sK4) ),
% 2.99/1.04      inference(superposition,[status(thm)],[c_766,c_769]) ).
% 2.99/1.04  
% 2.99/1.04  cnf(c_1341,plain,
% 2.99/1.04      ( k1_enumset1(sK2,sK2,sK2) = k1_xboole_0 | k1_relat_1(sK4) = sK1 ),
% 2.99/1.04      inference(superposition,[status(thm)],[c_349,c_1275]) ).
% 2.99/1.04  
% 2.99/1.04  cnf(c_3,plain,
% 2.99/1.04      ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) ),
% 2.99/1.04      inference(cnf_transformation,[],[f67]) ).
% 2.99/1.04  
% 2.99/1.04  cnf(c_773,plain,
% 2.99/1.04      ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) = iProver_top ),
% 2.99/1.04      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.99/1.04  
% 2.99/1.04  cnf(c_1345,plain,
% 2.99/1.04      ( k1_relat_1(sK4) = sK1
% 2.99/1.04      | r2_hidden(sK2,k1_xboole_0) = iProver_top ),
% 2.99/1.04      inference(superposition,[status(thm)],[c_1341,c_773]) ).
% 2.99/1.04  
% 2.99/1.04  cnf(c_0,plain,
% 2.99/1.04      ( r1_tarski(k1_xboole_0,X0) ),
% 2.99/1.04      inference(cnf_transformation,[],[f34]) ).
% 2.99/1.04  
% 2.99/1.04  cnf(c_7,plain,
% 2.99/1.04      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 2.99/1.04      inference(cnf_transformation,[],[f43]) ).
% 2.99/1.04  
% 2.99/1.04  cnf(c_252,plain,
% 2.99/1.04      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 2.99/1.04      inference(resolution_lifted,[status(thm)],[c_0,c_7]) ).
% 2.99/1.04  
% 2.99/1.04  cnf(c_253,plain,
% 2.99/1.04      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 2.99/1.04      inference(unflattening,[status(thm)],[c_252]) ).
% 2.99/1.04  
% 2.99/1.04  cnf(c_765,plain,
% 2.99/1.04      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.99/1.04      inference(predicate_to_equality,[status(thm)],[c_253]) ).
% 2.99/1.04  
% 2.99/1.04  cnf(c_1624,plain,
% 2.99/1.04      ( k1_relat_1(sK4) = sK1 ),
% 2.99/1.04      inference(forward_subsumption_resolution,
% 2.99/1.04                [status(thm)],
% 2.99/1.04                [c_1345,c_765]) ).
% 2.99/1.04  
% 2.99/1.04  cnf(c_8,plain,
% 2.99/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.99/1.04      | v1_relat_1(X0) ),
% 2.99/1.04      inference(cnf_transformation,[],[f44]) ).
% 2.99/1.04  
% 2.99/1.04  cnf(c_6,plain,
% 2.99/1.04      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.99/1.04      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 2.99/1.04      | ~ v1_relat_1(X1)
% 2.99/1.04      | ~ v1_funct_1(X1) ),
% 2.99/1.04      inference(cnf_transformation,[],[f42]) ).
% 2.99/1.04  
% 2.99/1.04  cnf(c_22,negated_conjecture,
% 2.99/1.04      ( v1_funct_1(sK4) ),
% 2.99/1.04      inference(cnf_transformation,[],[f54]) ).
% 2.99/1.04  
% 2.99/1.04  cnf(c_263,plain,
% 2.99/1.04      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.99/1.04      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 2.99/1.04      | ~ v1_relat_1(X1)
% 2.99/1.04      | sK4 != X1 ),
% 2.99/1.04      inference(resolution_lifted,[status(thm)],[c_6,c_22]) ).
% 2.99/1.04  
% 2.99/1.04  cnf(c_264,plain,
% 2.99/1.04      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 2.99/1.04      | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4))
% 2.99/1.04      | ~ v1_relat_1(sK4) ),
% 2.99/1.04      inference(unflattening,[status(thm)],[c_263]) ).
% 2.99/1.04  
% 2.99/1.04  cnf(c_282,plain,
% 2.99/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.99/1.04      | ~ r2_hidden(X3,k1_relat_1(sK4))
% 2.99/1.04      | r2_hidden(k1_funct_1(sK4,X3),k2_relat_1(sK4))
% 2.99/1.04      | sK4 != X0 ),
% 2.99/1.04      inference(resolution_lifted,[status(thm)],[c_8,c_264]) ).
% 2.99/1.04  
% 2.99/1.04  cnf(c_283,plain,
% 2.99/1.04      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.99/1.04      | ~ r2_hidden(X2,k1_relat_1(sK4))
% 2.99/1.04      | r2_hidden(k1_funct_1(sK4,X2),k2_relat_1(sK4)) ),
% 2.99/1.04      inference(unflattening,[status(thm)],[c_282]) ).
% 2.99/1.04  
% 2.99/1.04  cnf(c_468,plain,
% 2.99/1.04      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 2.99/1.04      | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4))
% 2.99/1.04      | ~ sP0_iProver_split ),
% 2.99/1.04      inference(splitting,
% 2.99/1.04                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.99/1.04                [c_283]) ).
% 2.99/1.04  
% 2.99/1.04  cnf(c_764,plain,
% 2.99/1.04      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.99/1.04      | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top
% 2.99/1.04      | sP0_iProver_split != iProver_top ),
% 2.99/1.04      inference(predicate_to_equality,[status(thm)],[c_468]) ).
% 2.99/1.04  
% 2.99/1.04  cnf(c_25,plain,
% 2.99/1.04      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_enumset1(sK2,sK2,sK2)))) = iProver_top ),
% 2.99/1.04      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.99/1.04  
% 2.99/1.04  cnf(c_470,plain,
% 2.99/1.04      ( sP1_iProver_split | sP0_iProver_split ),
% 2.99/1.04      inference(splitting,
% 2.99/1.04                [splitting(split),new_symbols(definition,[])],
% 2.99/1.04                [c_283]) ).
% 2.99/1.04  
% 2.99/1.04  cnf(c_496,plain,
% 2.99/1.04      ( sP1_iProver_split = iProver_top
% 2.99/1.04      | sP0_iProver_split = iProver_top ),
% 2.99/1.04      inference(predicate_to_equality,[status(thm)],[c_470]) ).
% 2.99/1.04  
% 2.99/1.04  cnf(c_500,plain,
% 2.99/1.04      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.99/1.04      | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top
% 2.99/1.04      | sP0_iProver_split != iProver_top ),
% 2.99/1.04      inference(predicate_to_equality,[status(thm)],[c_468]) ).
% 2.99/1.04  
% 2.99/1.04  cnf(c_469,plain,
% 2.99/1.04      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.99/1.04      | ~ sP1_iProver_split ),
% 2.99/1.04      inference(splitting,
% 2.99/1.04                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 2.99/1.04                [c_283]) ).
% 2.99/1.04  
% 2.99/1.04  cnf(c_886,plain,
% 2.99/1.04      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_enumset1(sK2,sK2,sK2))))
% 2.99/1.04      | ~ sP1_iProver_split ),
% 2.99/1.04      inference(instantiation,[status(thm)],[c_469]) ).
% 2.99/1.04  
% 2.99/1.04  cnf(c_887,plain,
% 2.99/1.04      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_enumset1(sK2,sK2,sK2)))) != iProver_top
% 2.99/1.04      | sP1_iProver_split != iProver_top ),
% 2.99/1.04      inference(predicate_to_equality,[status(thm)],[c_886]) ).
% 2.99/1.04  
% 2.99/1.04  cnf(c_1039,plain,
% 2.99/1.04      ( r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top
% 2.99/1.04      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
% 2.99/1.04      inference(global_propositional_subsumption,
% 2.99/1.04                [status(thm)],
% 2.99/1.04                [c_764,c_25,c_496,c_500,c_887]) ).
% 2.99/1.04  
% 2.99/1.04  cnf(c_1040,plain,
% 2.99/1.04      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.99/1.04      | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top ),
% 2.99/1.04      inference(renaming,[status(thm)],[c_1039]) ).
% 2.99/1.04  
% 2.99/1.04  cnf(c_1626,plain,
% 2.99/1.04      ( r2_hidden(X0,sK1) != iProver_top
% 2.99/1.04      | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top ),
% 2.99/1.04      inference(demodulation,[status(thm)],[c_1624,c_1040]) ).
% 2.99/1.04  
% 2.99/1.04  cnf(c_11,plain,
% 2.99/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.99/1.04      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.99/1.04      inference(cnf_transformation,[],[f47]) ).
% 2.99/1.04  
% 2.99/1.04  cnf(c_768,plain,
% 2.99/1.04      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.99/1.04      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.99/1.04      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.99/1.04  
% 2.99/1.04  cnf(c_1239,plain,
% 2.99/1.04      ( k2_relset_1(sK1,k1_enumset1(sK2,sK2,sK2),sK4) = k2_relat_1(sK4) ),
% 2.99/1.04      inference(superposition,[status(thm)],[c_766,c_768]) ).
% 2.99/1.04  
% 2.99/1.04  cnf(c_9,plain,
% 2.99/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.99/1.04      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 2.99/1.04      inference(cnf_transformation,[],[f45]) ).
% 2.99/1.04  
% 2.99/1.04  cnf(c_770,plain,
% 2.99/1.04      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.99/1.04      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 2.99/1.04      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.99/1.04  
% 2.99/1.04  cnf(c_1699,plain,
% 2.99/1.04      ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) = iProver_top
% 2.99/1.04      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_enumset1(sK2,sK2,sK2)))) != iProver_top ),
% 2.99/1.04      inference(superposition,[status(thm)],[c_1239,c_770]) ).
% 2.99/1.04  
% 2.99/1.04  cnf(c_2046,plain,
% 2.99/1.04      ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) = iProver_top ),
% 2.99/1.04      inference(global_propositional_subsumption,
% 2.99/1.04                [status(thm)],
% 2.99/1.04                [c_1699,c_25]) ).
% 2.99/1.04  
% 2.99/1.04  cnf(c_5,plain,
% 2.99/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.99/1.04      | ~ r2_hidden(X2,X0)
% 2.99/1.04      | r2_hidden(X2,X1) ),
% 2.99/1.04      inference(cnf_transformation,[],[f41]) ).
% 2.99/1.04  
% 2.99/1.04  cnf(c_771,plain,
% 2.99/1.04      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.99/1.04      | r2_hidden(X2,X0) != iProver_top
% 2.99/1.04      | r2_hidden(X2,X1) = iProver_top ),
% 2.99/1.04      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.99/1.04  
% 2.99/1.04  cnf(c_2052,plain,
% 2.99/1.04      ( r2_hidden(X0,k1_enumset1(sK2,sK2,sK2)) = iProver_top
% 2.99/1.04      | r2_hidden(X0,k2_relat_1(sK4)) != iProver_top ),
% 2.99/1.04      inference(superposition,[status(thm)],[c_2046,c_771]) ).
% 2.99/1.04  
% 2.99/1.04  cnf(c_4,plain,
% 2.99/1.04      ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X1)) | X0 = X1 ),
% 2.99/1.04      inference(cnf_transformation,[],[f68]) ).
% 2.99/1.04  
% 2.99/1.04  cnf(c_772,plain,
% 2.99/1.04      ( X0 = X1 | r2_hidden(X0,k1_enumset1(X1,X1,X1)) != iProver_top ),
% 2.99/1.04      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.99/1.04  
% 2.99/1.04  cnf(c_2274,plain,
% 2.99/1.04      ( sK2 = X0 | r2_hidden(X0,k2_relat_1(sK4)) != iProver_top ),
% 2.99/1.04      inference(superposition,[status(thm)],[c_2052,c_772]) ).
% 2.99/1.04  
% 2.99/1.04  cnf(c_2320,plain,
% 2.99/1.04      ( k1_funct_1(sK4,X0) = sK2 | r2_hidden(X0,sK1) != iProver_top ),
% 2.99/1.04      inference(superposition,[status(thm)],[c_1626,c_2274]) ).
% 2.99/1.04  
% 2.99/1.04  cnf(c_2339,plain,
% 2.99/1.04      ( k1_funct_1(sK4,sK3) = sK2 ),
% 2.99/1.04      inference(superposition,[status(thm)],[c_767,c_2320]) ).
% 2.99/1.04  
% 2.99/1.04  cnf(c_18,negated_conjecture,
% 2.99/1.04      ( k1_funct_1(sK4,sK3) != sK2 ),
% 2.99/1.04      inference(cnf_transformation,[],[f58]) ).
% 2.99/1.04  
% 2.99/1.04  cnf(contradiction,plain,
% 2.99/1.04      ( $false ),
% 2.99/1.04      inference(minisat,[status(thm)],[c_2339,c_18]) ).
% 2.99/1.04  
% 2.99/1.04  
% 2.99/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 2.99/1.04  
% 2.99/1.04  ------                               Statistics
% 2.99/1.04  
% 2.99/1.04  ------ General
% 2.99/1.04  
% 2.99/1.04  abstr_ref_over_cycles:                  0
% 2.99/1.04  abstr_ref_under_cycles:                 0
% 2.99/1.04  gc_basic_clause_elim:                   0
% 2.99/1.04  forced_gc_time:                         0
% 2.99/1.04  parsing_time:                           0.011
% 2.99/1.04  unif_index_cands_time:                  0.
% 2.99/1.04  unif_index_add_time:                    0.
% 2.99/1.04  orderings_time:                         0.
% 2.99/1.04  out_proof_time:                         0.013
% 2.99/1.04  total_time:                             0.12
% 2.99/1.04  num_of_symbols:                         53
% 2.99/1.04  num_of_terms:                           2736
% 2.99/1.04  
% 2.99/1.04  ------ Preprocessing
% 2.99/1.04  
% 2.99/1.04  num_of_splits:                          2
% 2.99/1.04  num_of_split_atoms:                     2
% 2.99/1.04  num_of_reused_defs:                     0
% 2.99/1.04  num_eq_ax_congr_red:                    21
% 2.99/1.04  num_of_sem_filtered_clauses:            1
% 2.99/1.04  num_of_subtypes:                        0
% 2.99/1.04  monotx_restored_types:                  0
% 2.99/1.04  sat_num_of_epr_types:                   0
% 2.99/1.04  sat_num_of_non_cyclic_types:            0
% 2.99/1.04  sat_guarded_non_collapsed_types:        0
% 2.99/1.04  num_pure_diseq_elim:                    0
% 2.99/1.04  simp_replaced_by:                       0
% 2.99/1.04  res_preprocessed:                       98
% 2.99/1.04  prep_upred:                             0
% 2.99/1.04  prep_unflattend:                        31
% 2.99/1.04  smt_new_axioms:                         0
% 2.99/1.04  pred_elim_cands:                        2
% 2.99/1.04  pred_elim:                              4
% 2.99/1.04  pred_elim_cl:                           7
% 2.99/1.04  pred_elim_cycles:                       6
% 2.99/1.04  merged_defs:                            0
% 2.99/1.04  merged_defs_ncl:                        0
% 2.99/1.04  bin_hyper_res:                          0
% 2.99/1.04  prep_cycles:                            4
% 2.99/1.04  pred_elim_time:                         0.003
% 2.99/1.04  splitting_time:                         0.
% 2.99/1.04  sem_filter_time:                        0.
% 2.99/1.04  monotx_time:                            0.
% 2.99/1.04  subtype_inf_time:                       0.
% 2.99/1.04  
% 2.99/1.04  ------ Problem properties
% 2.99/1.04  
% 2.99/1.04  clauses:                                18
% 2.99/1.04  conjectures:                            3
% 2.99/1.04  epr:                                    3
% 2.99/1.04  horn:                                   14
% 2.99/1.04  ground:                                 7
% 2.99/1.04  unary:                                  5
% 2.99/1.04  binary:                                 7
% 2.99/1.04  lits:                                   38
% 2.99/1.04  lits_eq:                                15
% 2.99/1.04  fd_pure:                                0
% 2.99/1.04  fd_pseudo:                              0
% 2.99/1.04  fd_cond:                                0
% 2.99/1.04  fd_pseudo_cond:                         2
% 2.99/1.04  ac_symbols:                             0
% 2.99/1.04  
% 2.99/1.04  ------ Propositional Solver
% 2.99/1.04  
% 2.99/1.04  prop_solver_calls:                      28
% 2.99/1.04  prop_fast_solver_calls:                 546
% 2.99/1.04  smt_solver_calls:                       0
% 2.99/1.04  smt_fast_solver_calls:                  0
% 2.99/1.04  prop_num_of_clauses:                    895
% 2.99/1.04  prop_preprocess_simplified:             3307
% 2.99/1.04  prop_fo_subsumed:                       7
% 2.99/1.04  prop_solver_time:                       0.
% 2.99/1.04  smt_solver_time:                        0.
% 2.99/1.04  smt_fast_solver_time:                   0.
% 2.99/1.04  prop_fast_solver_time:                  0.
% 2.99/1.04  prop_unsat_core_time:                   0.
% 2.99/1.04  
% 2.99/1.04  ------ QBF
% 2.99/1.04  
% 2.99/1.04  qbf_q_res:                              0
% 2.99/1.04  qbf_num_tautologies:                    0
% 2.99/1.04  qbf_prep_cycles:                        0
% 2.99/1.04  
% 2.99/1.04  ------ BMC1
% 2.99/1.04  
% 2.99/1.04  bmc1_current_bound:                     -1
% 2.99/1.04  bmc1_last_solved_bound:                 -1
% 2.99/1.04  bmc1_unsat_core_size:                   -1
% 2.99/1.04  bmc1_unsat_core_parents_size:           -1
% 2.99/1.04  bmc1_merge_next_fun:                    0
% 2.99/1.04  bmc1_unsat_core_clauses_time:           0.
% 2.99/1.04  
% 2.99/1.04  ------ Instantiation
% 2.99/1.04  
% 2.99/1.04  inst_num_of_clauses:                    281
% 2.99/1.04  inst_num_in_passive:                    125
% 2.99/1.04  inst_num_in_active:                     132
% 2.99/1.04  inst_num_in_unprocessed:                24
% 2.99/1.04  inst_num_of_loops:                      150
% 2.99/1.04  inst_num_of_learning_restarts:          0
% 2.99/1.04  inst_num_moves_active_passive:          15
% 2.99/1.04  inst_lit_activity:                      0
% 2.99/1.04  inst_lit_activity_moves:                0
% 2.99/1.04  inst_num_tautologies:                   0
% 2.99/1.04  inst_num_prop_implied:                  0
% 2.99/1.04  inst_num_existing_simplified:           0
% 2.99/1.04  inst_num_eq_res_simplified:             0
% 2.99/1.04  inst_num_child_elim:                    0
% 2.99/1.04  inst_num_of_dismatching_blockings:      91
% 2.99/1.04  inst_num_of_non_proper_insts:           242
% 2.99/1.04  inst_num_of_duplicates:                 0
% 2.99/1.04  inst_inst_num_from_inst_to_res:         0
% 2.99/1.04  inst_dismatching_checking_time:         0.
% 2.99/1.04  
% 2.99/1.04  ------ Resolution
% 2.99/1.04  
% 2.99/1.04  res_num_of_clauses:                     0
% 2.99/1.04  res_num_in_passive:                     0
% 2.99/1.04  res_num_in_active:                      0
% 2.99/1.04  res_num_of_loops:                       102
% 2.99/1.04  res_forward_subset_subsumed:            26
% 2.99/1.04  res_backward_subset_subsumed:           0
% 2.99/1.04  res_forward_subsumed:                   0
% 2.99/1.04  res_backward_subsumed:                  0
% 2.99/1.04  res_forward_subsumption_resolution:     0
% 2.99/1.04  res_backward_subsumption_resolution:    0
% 2.99/1.04  res_clause_to_clause_subsumption:       50
% 2.99/1.04  res_orphan_elimination:                 0
% 2.99/1.04  res_tautology_del:                      25
% 2.99/1.04  res_num_eq_res_simplified:              0
% 2.99/1.04  res_num_sel_changes:                    0
% 2.99/1.04  res_moves_from_active_to_pass:          0
% 2.99/1.04  
% 2.99/1.04  ------ Superposition
% 2.99/1.04  
% 2.99/1.04  sup_time_total:                         0.
% 2.99/1.04  sup_time_generating:                    0.
% 2.99/1.04  sup_time_sim_full:                      0.
% 2.99/1.04  sup_time_sim_immed:                     0.
% 2.99/1.04  
% 2.99/1.04  sup_num_of_clauses:                     35
% 2.99/1.04  sup_num_in_active:                      26
% 2.99/1.04  sup_num_in_passive:                     9
% 2.99/1.04  sup_num_of_loops:                       29
% 2.99/1.04  sup_fw_superposition:                   15
% 2.99/1.04  sup_bw_superposition:                   16
% 2.99/1.04  sup_immediate_simplified:               7
% 2.99/1.04  sup_given_eliminated:                   0
% 2.99/1.04  comparisons_done:                       0
% 2.99/1.04  comparisons_avoided:                    5
% 2.99/1.04  
% 2.99/1.04  ------ Simplifications
% 2.99/1.04  
% 2.99/1.04  
% 2.99/1.04  sim_fw_subset_subsumed:                 6
% 2.99/1.04  sim_bw_subset_subsumed:                 3
% 2.99/1.04  sim_fw_subsumed:                        0
% 2.99/1.04  sim_bw_subsumed:                        0
% 2.99/1.04  sim_fw_subsumption_res:                 2
% 2.99/1.04  sim_bw_subsumption_res:                 0
% 2.99/1.04  sim_tautology_del:                      0
% 2.99/1.04  sim_eq_tautology_del:                   1
% 2.99/1.04  sim_eq_res_simp:                        0
% 2.99/1.04  sim_fw_demodulated:                     0
% 2.99/1.04  sim_bw_demodulated:                     2
% 2.99/1.04  sim_light_normalised:                   0
% 2.99/1.04  sim_joinable_taut:                      0
% 2.99/1.04  sim_joinable_simp:                      0
% 2.99/1.04  sim_ac_normalised:                      0
% 2.99/1.04  sim_smt_subsumption:                    0
% 2.99/1.04  
%------------------------------------------------------------------------------
