%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:19 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 573 expanded)
%              Number of clauses        :   64 ( 155 expanded)
%              Number of leaves         :   15 ( 134 expanded)
%              Depth                    :   19
%              Number of atoms          :  331 (1646 expanded)
%              Number of equality atoms :  200 ( 815 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( k1_tarski(k1_funct_1(sK3,sK1)) != k2_relset_1(k1_tarski(sK1),sK2,sK3)
      & k1_xboole_0 != sK2
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
      & v1_funct_2(sK3,k1_tarski(sK1),sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( k1_tarski(k1_funct_1(sK3,sK1)) != k2_relset_1(k1_tarski(sK1),sK2,sK3)
    & k1_xboole_0 != sK2
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
    & v1_funct_2(sK3,k1_tarski(sK1),sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f23,f29])).

fof(f50,plain,(
    v1_funct_2(sK3,k1_tarski(sK1),sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f54,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f35,f36])).

fof(f63,plain,(
    v1_funct_2(sK3,k1_enumset1(sK1,sK1,sK1),sK2) ),
    inference(definition_unfolding,[],[f50,f54])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

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
    inference(nnf_transformation,[],[f21])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f51,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) ),
    inference(cnf_transformation,[],[f30])).

fof(f62,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))) ),
    inference(definition_unfolding,[],[f51,f54])).

fof(f52,plain,(
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

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f26,plain,(
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

fof(f27,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f32,f54])).

fof(f64,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_enumset1(X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f57])).

fof(f65,plain,(
    ! [X3] : r2_hidden(X3,k1_enumset1(X3,X3,X3)) ),
    inference(equality_resolution,[],[f64])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f39,f54])).

fof(f49,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_enumset1(X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f37,f54])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f38,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f53,plain,(
    k1_tarski(k1_funct_1(sK3,sK1)) != k2_relset_1(k1_tarski(sK1),sK2,sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f61,plain,(
    k1_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK3) ),
    inference(definition_unfolding,[],[f53,f54,f54])).

cnf(c_19,negated_conjecture,
    ( v1_funct_2(sK3,k1_enumset1(sK1,sK1,sK1),sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_370,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_18])).

cnf(c_371,plain,
    ( ~ v1_funct_2(sK3,X0,X1)
    | k1_relset_1(X0,X1,sK3) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_370])).

cnf(c_657,plain,
    ( k1_relset_1(X0,X1,sK3) = X0
    | k1_enumset1(sK1,sK1,sK1) != X0
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK2 != X1
    | sK3 != sK3
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_371])).

cnf(c_658,plain,
    ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK3) = k1_enumset1(sK1,sK1,sK1)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_657])).

cnf(c_17,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_659,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))
    | k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK3) = k1_enumset1(sK1,sK1,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_658,c_17])).

cnf(c_660,plain,
    ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK3) = k1_enumset1(sK1,sK1,sK1)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
    inference(renaming,[status(thm)],[c_659])).

cnf(c_714,plain,
    ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK3) = k1_enumset1(sK1,sK1,sK1) ),
    inference(equality_resolution_simp,[status(thm)],[c_660])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_415,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_18])).

cnf(c_416,plain,
    ( k1_relset_1(X0,X1,sK3) = k1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_415])).

cnf(c_1158,plain,
    ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK3) = k1_relat_1(sK3) ),
    inference(equality_resolution,[status(thm)],[c_416])).

cnf(c_1402,plain,
    ( k1_enumset1(sK1,sK1,sK1) = k1_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_714,c_1158])).

cnf(c_2,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1023,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1429,plain,
    ( r2_hidden(sK1,k1_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1402,c_1023])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_424,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_18])).

cnf(c_425,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_424])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_225,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_20])).

cnf(c_226,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_225])).

cnf(c_536,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
    inference(resolution,[status(thm)],[c_425,c_226])).

cnf(c_829,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_536])).

cnf(c_1020,plain,
    ( k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_829])).

cnf(c_830,plain,
    ( sP2_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_536])).

cnf(c_865,plain,
    ( sP2_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_830])).

cnf(c_866,plain,
    ( k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_829])).

cnf(c_832,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1119,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) = k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_832])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_enumset1(X1,X1,X1)) = k11_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_559,plain,
    ( k9_relat_1(X0,k1_enumset1(X1,X1,X1)) = k11_relat_1(X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_425])).

cnf(c_560,plain,
    ( k9_relat_1(sK3,k1_enumset1(X0,X0,X0)) = k11_relat_1(sK3,X0)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
    inference(unflattening,[status(thm)],[c_559])).

cnf(c_826,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_560])).

cnf(c_1120,plain,
    ( ~ sP0_iProver_split
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_826])).

cnf(c_1124,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1120])).

cnf(c_2171,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1020,c_865,c_866,c_1119,c_1124])).

cnf(c_2172,plain,
    ( k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2171])).

cnf(c_2180,plain,
    ( k1_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) = k11_relat_1(sK3,sK1) ),
    inference(superposition,[status(thm)],[c_1429,c_2172])).

cnf(c_827,plain,
    ( k9_relat_1(sK3,k1_enumset1(X0,X0,X0)) = k11_relat_1(sK3,X0)
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_560])).

cnf(c_1017,plain,
    ( k9_relat_1(sK3,k1_enumset1(X0,X0,X0)) = k11_relat_1(sK3,X0)
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_827])).

cnf(c_828,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_560])).

cnf(c_1790,plain,
    ( k9_relat_1(sK3,k1_enumset1(X0,X0,X0)) = k11_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1017,c_828,c_827,c_1119,c_1120])).

cnf(c_1794,plain,
    ( k9_relat_1(sK3,k1_relat_1(sK3)) = k11_relat_1(sK3,sK1) ),
    inference(superposition,[status(thm)],[c_1402,c_1790])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_550,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_425])).

cnf(c_551,plain,
    ( k9_relat_1(sK3,k1_relat_1(sK3)) = k2_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_550])).

cnf(c_1121,plain,
    ( k9_relat_1(sK3,k1_relat_1(sK3)) = k2_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_551])).

cnf(c_1248,plain,
    ( k9_relat_1(sK3,k1_relat_1(sK3)) = k2_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_551,c_1119,c_1121])).

cnf(c_1795,plain,
    ( k11_relat_1(sK3,sK1) = k2_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_1794,c_1248])).

cnf(c_2182,plain,
    ( k1_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) = k2_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_2180,c_1795])).

cnf(c_833,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1145,plain,
    ( k2_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK3) != X0
    | k1_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != X0
    | k1_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) = k2_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_833])).

cnf(c_1201,plain,
    ( k2_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK3) != k2_relat_1(sK3)
    | k1_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) = k2_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK3)
    | k1_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1145])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_406,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_18])).

cnf(c_407,plain,
    ( k2_relset_1(X0,X1,sK3) = k2_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_406])).

cnf(c_1123,plain,
    ( k2_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK3) = k2_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_407])).

cnf(c_16,negated_conjecture,
    ( k1_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2182,c_1201,c_1123,c_1119,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:06:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 2.13/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/0.99  
% 2.13/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.13/0.99  
% 2.13/0.99  ------  iProver source info
% 2.13/0.99  
% 2.13/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.13/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.13/0.99  git: non_committed_changes: false
% 2.13/0.99  git: last_make_outside_of_git: false
% 2.13/0.99  
% 2.13/0.99  ------ 
% 2.13/0.99  
% 2.13/0.99  ------ Input Options
% 2.13/0.99  
% 2.13/0.99  --out_options                           all
% 2.13/0.99  --tptp_safe_out                         true
% 2.13/0.99  --problem_path                          ""
% 2.13/0.99  --include_path                          ""
% 2.13/0.99  --clausifier                            res/vclausify_rel
% 2.13/0.99  --clausifier_options                    --mode clausify
% 2.13/0.99  --stdin                                 false
% 2.13/0.99  --stats_out                             all
% 2.13/0.99  
% 2.13/0.99  ------ General Options
% 2.13/0.99  
% 2.13/0.99  --fof                                   false
% 2.13/0.99  --time_out_real                         305.
% 2.13/0.99  --time_out_virtual                      -1.
% 2.13/0.99  --symbol_type_check                     false
% 2.13/0.99  --clausify_out                          false
% 2.13/0.99  --sig_cnt_out                           false
% 2.13/0.99  --trig_cnt_out                          false
% 2.13/0.99  --trig_cnt_out_tolerance                1.
% 2.13/0.99  --trig_cnt_out_sk_spl                   false
% 2.13/0.99  --abstr_cl_out                          false
% 2.13/0.99  
% 2.13/0.99  ------ Global Options
% 2.13/0.99  
% 2.13/0.99  --schedule                              default
% 2.13/0.99  --add_important_lit                     false
% 2.13/0.99  --prop_solver_per_cl                    1000
% 2.13/0.99  --min_unsat_core                        false
% 2.13/0.99  --soft_assumptions                      false
% 2.13/0.99  --soft_lemma_size                       3
% 2.13/0.99  --prop_impl_unit_size                   0
% 2.13/0.99  --prop_impl_unit                        []
% 2.13/0.99  --share_sel_clauses                     true
% 2.13/0.99  --reset_solvers                         false
% 2.13/0.99  --bc_imp_inh                            [conj_cone]
% 2.13/0.99  --conj_cone_tolerance                   3.
% 2.13/0.99  --extra_neg_conj                        none
% 2.13/0.99  --large_theory_mode                     true
% 2.13/0.99  --prolific_symb_bound                   200
% 2.13/0.99  --lt_threshold                          2000
% 2.13/0.99  --clause_weak_htbl                      true
% 2.13/0.99  --gc_record_bc_elim                     false
% 2.13/0.99  
% 2.13/0.99  ------ Preprocessing Options
% 2.13/0.99  
% 2.13/0.99  --preprocessing_flag                    true
% 2.13/0.99  --time_out_prep_mult                    0.1
% 2.13/0.99  --splitting_mode                        input
% 2.13/0.99  --splitting_grd                         true
% 2.13/0.99  --splitting_cvd                         false
% 2.13/0.99  --splitting_cvd_svl                     false
% 2.13/0.99  --splitting_nvd                         32
% 2.13/0.99  --sub_typing                            true
% 2.13/0.99  --prep_gs_sim                           true
% 2.13/0.99  --prep_unflatten                        true
% 2.13/0.99  --prep_res_sim                          true
% 2.13/0.99  --prep_upred                            true
% 2.13/0.99  --prep_sem_filter                       exhaustive
% 2.13/0.99  --prep_sem_filter_out                   false
% 2.13/0.99  --pred_elim                             true
% 2.13/0.99  --res_sim_input                         true
% 2.13/0.99  --eq_ax_congr_red                       true
% 2.13/0.99  --pure_diseq_elim                       true
% 2.13/0.99  --brand_transform                       false
% 2.13/0.99  --non_eq_to_eq                          false
% 2.13/0.99  --prep_def_merge                        true
% 2.13/0.99  --prep_def_merge_prop_impl              false
% 2.13/0.99  --prep_def_merge_mbd                    true
% 2.13/0.99  --prep_def_merge_tr_red                 false
% 2.13/0.99  --prep_def_merge_tr_cl                  false
% 2.13/0.99  --smt_preprocessing                     true
% 2.13/0.99  --smt_ac_axioms                         fast
% 2.13/0.99  --preprocessed_out                      false
% 2.13/0.99  --preprocessed_stats                    false
% 2.13/0.99  
% 2.13/0.99  ------ Abstraction refinement Options
% 2.13/0.99  
% 2.13/0.99  --abstr_ref                             []
% 2.13/0.99  --abstr_ref_prep                        false
% 2.13/0.99  --abstr_ref_until_sat                   false
% 2.13/0.99  --abstr_ref_sig_restrict                funpre
% 2.13/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.13/0.99  --abstr_ref_under                       []
% 2.13/0.99  
% 2.13/0.99  ------ SAT Options
% 2.13/0.99  
% 2.13/0.99  --sat_mode                              false
% 2.13/0.99  --sat_fm_restart_options                ""
% 2.13/0.99  --sat_gr_def                            false
% 2.13/0.99  --sat_epr_types                         true
% 2.13/0.99  --sat_non_cyclic_types                  false
% 2.13/0.99  --sat_finite_models                     false
% 2.13/0.99  --sat_fm_lemmas                         false
% 2.13/0.99  --sat_fm_prep                           false
% 2.13/0.99  --sat_fm_uc_incr                        true
% 2.13/0.99  --sat_out_model                         small
% 2.13/0.99  --sat_out_clauses                       false
% 2.13/0.99  
% 2.13/0.99  ------ QBF Options
% 2.13/0.99  
% 2.13/0.99  --qbf_mode                              false
% 2.13/0.99  --qbf_elim_univ                         false
% 2.13/0.99  --qbf_dom_inst                          none
% 2.13/0.99  --qbf_dom_pre_inst                      false
% 2.13/0.99  --qbf_sk_in                             false
% 2.13/0.99  --qbf_pred_elim                         true
% 2.13/0.99  --qbf_split                             512
% 2.13/0.99  
% 2.13/0.99  ------ BMC1 Options
% 2.13/0.99  
% 2.13/0.99  --bmc1_incremental                      false
% 2.13/0.99  --bmc1_axioms                           reachable_all
% 2.13/0.99  --bmc1_min_bound                        0
% 2.13/0.99  --bmc1_max_bound                        -1
% 2.13/0.99  --bmc1_max_bound_default                -1
% 2.13/0.99  --bmc1_symbol_reachability              true
% 2.13/0.99  --bmc1_property_lemmas                  false
% 2.13/0.99  --bmc1_k_induction                      false
% 2.13/0.99  --bmc1_non_equiv_states                 false
% 2.13/0.99  --bmc1_deadlock                         false
% 2.13/0.99  --bmc1_ucm                              false
% 2.13/0.99  --bmc1_add_unsat_core                   none
% 2.13/0.99  --bmc1_unsat_core_children              false
% 2.13/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.13/0.99  --bmc1_out_stat                         full
% 2.13/0.99  --bmc1_ground_init                      false
% 2.13/0.99  --bmc1_pre_inst_next_state              false
% 2.13/0.99  --bmc1_pre_inst_state                   false
% 2.13/0.99  --bmc1_pre_inst_reach_state             false
% 2.13/0.99  --bmc1_out_unsat_core                   false
% 2.13/0.99  --bmc1_aig_witness_out                  false
% 2.13/0.99  --bmc1_verbose                          false
% 2.13/0.99  --bmc1_dump_clauses_tptp                false
% 2.13/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.13/0.99  --bmc1_dump_file                        -
% 2.13/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.13/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.13/0.99  --bmc1_ucm_extend_mode                  1
% 2.13/0.99  --bmc1_ucm_init_mode                    2
% 2.13/0.99  --bmc1_ucm_cone_mode                    none
% 2.13/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.13/0.99  --bmc1_ucm_relax_model                  4
% 2.13/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.13/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.13/0.99  --bmc1_ucm_layered_model                none
% 2.13/0.99  --bmc1_ucm_max_lemma_size               10
% 2.13/0.99  
% 2.13/0.99  ------ AIG Options
% 2.13/0.99  
% 2.13/0.99  --aig_mode                              false
% 2.13/0.99  
% 2.13/0.99  ------ Instantiation Options
% 2.13/0.99  
% 2.13/0.99  --instantiation_flag                    true
% 2.13/0.99  --inst_sos_flag                         false
% 2.13/0.99  --inst_sos_phase                        true
% 2.13/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.13/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.13/0.99  --inst_lit_sel_side                     num_symb
% 2.13/0.99  --inst_solver_per_active                1400
% 2.13/0.99  --inst_solver_calls_frac                1.
% 2.13/0.99  --inst_passive_queue_type               priority_queues
% 2.13/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.13/0.99  --inst_passive_queues_freq              [25;2]
% 2.13/0.99  --inst_dismatching                      true
% 2.13/0.99  --inst_eager_unprocessed_to_passive     true
% 2.13/0.99  --inst_prop_sim_given                   true
% 2.13/0.99  --inst_prop_sim_new                     false
% 2.13/0.99  --inst_subs_new                         false
% 2.13/0.99  --inst_eq_res_simp                      false
% 2.13/0.99  --inst_subs_given                       false
% 2.13/0.99  --inst_orphan_elimination               true
% 2.13/0.99  --inst_learning_loop_flag               true
% 2.13/0.99  --inst_learning_start                   3000
% 2.13/0.99  --inst_learning_factor                  2
% 2.13/0.99  --inst_start_prop_sim_after_learn       3
% 2.13/0.99  --inst_sel_renew                        solver
% 2.13/0.99  --inst_lit_activity_flag                true
% 2.13/0.99  --inst_restr_to_given                   false
% 2.13/0.99  --inst_activity_threshold               500
% 2.13/0.99  --inst_out_proof                        true
% 2.13/0.99  
% 2.13/0.99  ------ Resolution Options
% 2.13/0.99  
% 2.13/0.99  --resolution_flag                       true
% 2.13/0.99  --res_lit_sel                           adaptive
% 2.13/0.99  --res_lit_sel_side                      none
% 2.13/0.99  --res_ordering                          kbo
% 2.13/0.99  --res_to_prop_solver                    active
% 2.13/0.99  --res_prop_simpl_new                    false
% 2.13/0.99  --res_prop_simpl_given                  true
% 2.13/0.99  --res_passive_queue_type                priority_queues
% 2.13/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.13/0.99  --res_passive_queues_freq               [15;5]
% 2.13/0.99  --res_forward_subs                      full
% 2.13/0.99  --res_backward_subs                     full
% 2.13/0.99  --res_forward_subs_resolution           true
% 2.13/0.99  --res_backward_subs_resolution          true
% 2.13/0.99  --res_orphan_elimination                true
% 2.13/0.99  --res_time_limit                        2.
% 2.13/0.99  --res_out_proof                         true
% 2.13/0.99  
% 2.13/0.99  ------ Superposition Options
% 2.13/0.99  
% 2.13/0.99  --superposition_flag                    true
% 2.13/0.99  --sup_passive_queue_type                priority_queues
% 2.13/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.13/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.13/0.99  --demod_completeness_check              fast
% 2.13/0.99  --demod_use_ground                      true
% 2.13/0.99  --sup_to_prop_solver                    passive
% 2.13/0.99  --sup_prop_simpl_new                    true
% 2.13/0.99  --sup_prop_simpl_given                  true
% 2.13/0.99  --sup_fun_splitting                     false
% 2.13/0.99  --sup_smt_interval                      50000
% 2.13/0.99  
% 2.13/0.99  ------ Superposition Simplification Setup
% 2.13/0.99  
% 2.13/0.99  --sup_indices_passive                   []
% 2.13/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.13/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.13/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.13/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.13/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.13/0.99  --sup_full_bw                           [BwDemod]
% 2.13/0.99  --sup_immed_triv                        [TrivRules]
% 2.13/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.13/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.13/0.99  --sup_immed_bw_main                     []
% 2.13/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.13/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.13/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.13/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.13/0.99  
% 2.13/0.99  ------ Combination Options
% 2.13/0.99  
% 2.13/0.99  --comb_res_mult                         3
% 2.13/0.99  --comb_sup_mult                         2
% 2.13/0.99  --comb_inst_mult                        10
% 2.13/0.99  
% 2.13/0.99  ------ Debug Options
% 2.13/0.99  
% 2.13/0.99  --dbg_backtrace                         false
% 2.13/0.99  --dbg_dump_prop_clauses                 false
% 2.13/0.99  --dbg_dump_prop_clauses_file            -
% 2.13/0.99  --dbg_out_stat                          false
% 2.13/0.99  ------ Parsing...
% 2.13/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.13/0.99  
% 2.13/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.13/0.99  
% 2.13/0.99  ------ Preprocessing... gs_s  sp: 4 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.13/0.99  
% 2.13/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.13/0.99  ------ Proving...
% 2.13/0.99  ------ Problem Properties 
% 2.13/0.99  
% 2.13/0.99  
% 2.13/0.99  clauses                                 18
% 2.13/0.99  conjectures                             2
% 2.13/0.99  EPR                                     3
% 2.13/0.99  Horn                                    14
% 2.13/0.99  unary                                   4
% 2.13/0.99  binary                                  9
% 2.13/0.99  lits                                    38
% 2.13/0.99  lits eq                                 25
% 2.13/0.99  fd_pure                                 0
% 2.13/0.99  fd_pseudo                               0
% 2.13/0.99  fd_cond                                 0
% 2.13/0.99  fd_pseudo_cond                          2
% 2.13/0.99  AC symbols                              0
% 2.13/0.99  
% 2.13/0.99  ------ Schedule dynamic 5 is on 
% 2.13/0.99  
% 2.13/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.13/0.99  
% 2.13/0.99  
% 2.13/0.99  ------ 
% 2.13/0.99  Current options:
% 2.13/0.99  ------ 
% 2.13/0.99  
% 2.13/0.99  ------ Input Options
% 2.13/0.99  
% 2.13/0.99  --out_options                           all
% 2.13/0.99  --tptp_safe_out                         true
% 2.13/0.99  --problem_path                          ""
% 2.13/0.99  --include_path                          ""
% 2.13/0.99  --clausifier                            res/vclausify_rel
% 2.13/0.99  --clausifier_options                    --mode clausify
% 2.13/0.99  --stdin                                 false
% 2.13/0.99  --stats_out                             all
% 2.13/0.99  
% 2.13/0.99  ------ General Options
% 2.13/0.99  
% 2.13/0.99  --fof                                   false
% 2.13/0.99  --time_out_real                         305.
% 2.13/0.99  --time_out_virtual                      -1.
% 2.13/0.99  --symbol_type_check                     false
% 2.13/0.99  --clausify_out                          false
% 2.13/0.99  --sig_cnt_out                           false
% 2.13/0.99  --trig_cnt_out                          false
% 2.13/0.99  --trig_cnt_out_tolerance                1.
% 2.13/0.99  --trig_cnt_out_sk_spl                   false
% 2.13/0.99  --abstr_cl_out                          false
% 2.13/0.99  
% 2.13/0.99  ------ Global Options
% 2.13/0.99  
% 2.13/0.99  --schedule                              default
% 2.13/0.99  --add_important_lit                     false
% 2.13/0.99  --prop_solver_per_cl                    1000
% 2.13/0.99  --min_unsat_core                        false
% 2.13/0.99  --soft_assumptions                      false
% 2.13/0.99  --soft_lemma_size                       3
% 2.13/0.99  --prop_impl_unit_size                   0
% 2.13/0.99  --prop_impl_unit                        []
% 2.13/0.99  --share_sel_clauses                     true
% 2.13/0.99  --reset_solvers                         false
% 2.13/0.99  --bc_imp_inh                            [conj_cone]
% 2.13/0.99  --conj_cone_tolerance                   3.
% 2.13/0.99  --extra_neg_conj                        none
% 2.13/0.99  --large_theory_mode                     true
% 2.13/0.99  --prolific_symb_bound                   200
% 2.13/0.99  --lt_threshold                          2000
% 2.13/0.99  --clause_weak_htbl                      true
% 2.13/0.99  --gc_record_bc_elim                     false
% 2.13/0.99  
% 2.13/0.99  ------ Preprocessing Options
% 2.13/0.99  
% 2.13/0.99  --preprocessing_flag                    true
% 2.13/0.99  --time_out_prep_mult                    0.1
% 2.13/0.99  --splitting_mode                        input
% 2.13/0.99  --splitting_grd                         true
% 2.13/0.99  --splitting_cvd                         false
% 2.13/0.99  --splitting_cvd_svl                     false
% 2.13/0.99  --splitting_nvd                         32
% 2.13/0.99  --sub_typing                            true
% 2.13/0.99  --prep_gs_sim                           true
% 2.13/0.99  --prep_unflatten                        true
% 2.13/0.99  --prep_res_sim                          true
% 2.13/0.99  --prep_upred                            true
% 2.13/0.99  --prep_sem_filter                       exhaustive
% 2.13/0.99  --prep_sem_filter_out                   false
% 2.13/0.99  --pred_elim                             true
% 2.13/0.99  --res_sim_input                         true
% 2.13/0.99  --eq_ax_congr_red                       true
% 2.13/0.99  --pure_diseq_elim                       true
% 2.13/0.99  --brand_transform                       false
% 2.13/0.99  --non_eq_to_eq                          false
% 2.13/0.99  --prep_def_merge                        true
% 2.13/0.99  --prep_def_merge_prop_impl              false
% 2.13/0.99  --prep_def_merge_mbd                    true
% 2.13/0.99  --prep_def_merge_tr_red                 false
% 2.13/0.99  --prep_def_merge_tr_cl                  false
% 2.13/0.99  --smt_preprocessing                     true
% 2.13/0.99  --smt_ac_axioms                         fast
% 2.13/0.99  --preprocessed_out                      false
% 2.13/0.99  --preprocessed_stats                    false
% 2.13/0.99  
% 2.13/0.99  ------ Abstraction refinement Options
% 2.13/0.99  
% 2.13/0.99  --abstr_ref                             []
% 2.13/0.99  --abstr_ref_prep                        false
% 2.13/0.99  --abstr_ref_until_sat                   false
% 2.13/0.99  --abstr_ref_sig_restrict                funpre
% 2.13/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.13/0.99  --abstr_ref_under                       []
% 2.13/0.99  
% 2.13/0.99  ------ SAT Options
% 2.13/0.99  
% 2.13/0.99  --sat_mode                              false
% 2.13/0.99  --sat_fm_restart_options                ""
% 2.13/0.99  --sat_gr_def                            false
% 2.13/0.99  --sat_epr_types                         true
% 2.13/0.99  --sat_non_cyclic_types                  false
% 2.13/0.99  --sat_finite_models                     false
% 2.13/0.99  --sat_fm_lemmas                         false
% 2.13/0.99  --sat_fm_prep                           false
% 2.13/0.99  --sat_fm_uc_incr                        true
% 2.13/0.99  --sat_out_model                         small
% 2.13/0.99  --sat_out_clauses                       false
% 2.13/0.99  
% 2.13/0.99  ------ QBF Options
% 2.13/0.99  
% 2.13/0.99  --qbf_mode                              false
% 2.13/0.99  --qbf_elim_univ                         false
% 2.13/0.99  --qbf_dom_inst                          none
% 2.13/0.99  --qbf_dom_pre_inst                      false
% 2.13/0.99  --qbf_sk_in                             false
% 2.13/0.99  --qbf_pred_elim                         true
% 2.13/0.99  --qbf_split                             512
% 2.13/0.99  
% 2.13/0.99  ------ BMC1 Options
% 2.13/0.99  
% 2.13/0.99  --bmc1_incremental                      false
% 2.13/0.99  --bmc1_axioms                           reachable_all
% 2.13/0.99  --bmc1_min_bound                        0
% 2.13/0.99  --bmc1_max_bound                        -1
% 2.13/0.99  --bmc1_max_bound_default                -1
% 2.13/0.99  --bmc1_symbol_reachability              true
% 2.13/0.99  --bmc1_property_lemmas                  false
% 2.13/0.99  --bmc1_k_induction                      false
% 2.13/0.99  --bmc1_non_equiv_states                 false
% 2.13/0.99  --bmc1_deadlock                         false
% 2.13/0.99  --bmc1_ucm                              false
% 2.13/0.99  --bmc1_add_unsat_core                   none
% 2.13/0.99  --bmc1_unsat_core_children              false
% 2.13/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.13/0.99  --bmc1_out_stat                         full
% 2.13/0.99  --bmc1_ground_init                      false
% 2.13/0.99  --bmc1_pre_inst_next_state              false
% 2.13/0.99  --bmc1_pre_inst_state                   false
% 2.13/0.99  --bmc1_pre_inst_reach_state             false
% 2.13/0.99  --bmc1_out_unsat_core                   false
% 2.13/0.99  --bmc1_aig_witness_out                  false
% 2.13/0.99  --bmc1_verbose                          false
% 2.13/0.99  --bmc1_dump_clauses_tptp                false
% 2.13/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.13/0.99  --bmc1_dump_file                        -
% 2.13/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.13/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.13/0.99  --bmc1_ucm_extend_mode                  1
% 2.13/0.99  --bmc1_ucm_init_mode                    2
% 2.13/0.99  --bmc1_ucm_cone_mode                    none
% 2.13/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.13/0.99  --bmc1_ucm_relax_model                  4
% 2.13/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.13/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.13/0.99  --bmc1_ucm_layered_model                none
% 2.13/0.99  --bmc1_ucm_max_lemma_size               10
% 2.13/0.99  
% 2.13/0.99  ------ AIG Options
% 2.13/0.99  
% 2.13/0.99  --aig_mode                              false
% 2.13/0.99  
% 2.13/0.99  ------ Instantiation Options
% 2.13/0.99  
% 2.13/0.99  --instantiation_flag                    true
% 2.13/0.99  --inst_sos_flag                         false
% 2.13/0.99  --inst_sos_phase                        true
% 2.13/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.13/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.13/0.99  --inst_lit_sel_side                     none
% 2.13/0.99  --inst_solver_per_active                1400
% 2.13/0.99  --inst_solver_calls_frac                1.
% 2.13/0.99  --inst_passive_queue_type               priority_queues
% 2.13/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.13/0.99  --inst_passive_queues_freq              [25;2]
% 2.13/0.99  --inst_dismatching                      true
% 2.13/0.99  --inst_eager_unprocessed_to_passive     true
% 2.13/0.99  --inst_prop_sim_given                   true
% 2.13/0.99  --inst_prop_sim_new                     false
% 2.13/0.99  --inst_subs_new                         false
% 2.13/0.99  --inst_eq_res_simp                      false
% 2.13/0.99  --inst_subs_given                       false
% 2.13/0.99  --inst_orphan_elimination               true
% 2.13/0.99  --inst_learning_loop_flag               true
% 2.13/0.99  --inst_learning_start                   3000
% 2.13/0.99  --inst_learning_factor                  2
% 2.13/0.99  --inst_start_prop_sim_after_learn       3
% 2.13/0.99  --inst_sel_renew                        solver
% 2.13/0.99  --inst_lit_activity_flag                true
% 2.13/0.99  --inst_restr_to_given                   false
% 2.13/0.99  --inst_activity_threshold               500
% 2.13/0.99  --inst_out_proof                        true
% 2.13/0.99  
% 2.13/0.99  ------ Resolution Options
% 2.13/0.99  
% 2.13/0.99  --resolution_flag                       false
% 2.13/0.99  --res_lit_sel                           adaptive
% 2.13/0.99  --res_lit_sel_side                      none
% 2.13/0.99  --res_ordering                          kbo
% 2.13/0.99  --res_to_prop_solver                    active
% 2.13/0.99  --res_prop_simpl_new                    false
% 2.13/0.99  --res_prop_simpl_given                  true
% 2.13/0.99  --res_passive_queue_type                priority_queues
% 2.13/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.13/0.99  --res_passive_queues_freq               [15;5]
% 2.13/0.99  --res_forward_subs                      full
% 2.13/0.99  --res_backward_subs                     full
% 2.13/0.99  --res_forward_subs_resolution           true
% 2.13/0.99  --res_backward_subs_resolution          true
% 2.13/0.99  --res_orphan_elimination                true
% 2.13/0.99  --res_time_limit                        2.
% 2.13/0.99  --res_out_proof                         true
% 2.13/0.99  
% 2.13/0.99  ------ Superposition Options
% 2.13/0.99  
% 2.13/0.99  --superposition_flag                    true
% 2.13/0.99  --sup_passive_queue_type                priority_queues
% 2.13/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.13/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.13/0.99  --demod_completeness_check              fast
% 2.13/0.99  --demod_use_ground                      true
% 2.13/0.99  --sup_to_prop_solver                    passive
% 2.13/0.99  --sup_prop_simpl_new                    true
% 2.13/0.99  --sup_prop_simpl_given                  true
% 2.13/0.99  --sup_fun_splitting                     false
% 2.13/0.99  --sup_smt_interval                      50000
% 2.13/0.99  
% 2.13/0.99  ------ Superposition Simplification Setup
% 2.13/0.99  
% 2.13/0.99  --sup_indices_passive                   []
% 2.13/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.13/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.13/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.13/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.13/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.13/0.99  --sup_full_bw                           [BwDemod]
% 2.13/0.99  --sup_immed_triv                        [TrivRules]
% 2.13/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.13/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.13/0.99  --sup_immed_bw_main                     []
% 2.13/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.13/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.13/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.13/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.13/0.99  
% 2.13/0.99  ------ Combination Options
% 2.13/0.99  
% 2.13/0.99  --comb_res_mult                         3
% 2.13/0.99  --comb_sup_mult                         2
% 2.13/0.99  --comb_inst_mult                        10
% 2.13/0.99  
% 2.13/0.99  ------ Debug Options
% 2.13/0.99  
% 2.13/0.99  --dbg_backtrace                         false
% 2.13/0.99  --dbg_dump_prop_clauses                 false
% 2.13/0.99  --dbg_dump_prop_clauses_file            -
% 2.13/0.99  --dbg_out_stat                          false
% 2.13/0.99  
% 2.13/0.99  
% 2.13/0.99  
% 2.13/0.99  
% 2.13/0.99  ------ Proving...
% 2.13/0.99  
% 2.13/0.99  
% 2.13/0.99  % SZS status Theorem for theBenchmark.p
% 2.13/0.99  
% 2.13/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.13/0.99  
% 2.13/0.99  fof(f11,conjecture,(
% 2.13/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 2.13/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.13/0.99  
% 2.13/0.99  fof(f12,negated_conjecture,(
% 2.13/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 2.13/0.99    inference(negated_conjecture,[],[f11])).
% 2.13/0.99  
% 2.13/0.99  fof(f22,plain,(
% 2.13/0.99    ? [X0,X1,X2] : ((k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 2.13/0.99    inference(ennf_transformation,[],[f12])).
% 2.13/0.99  
% 2.13/0.99  fof(f23,plain,(
% 2.13/0.99    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 2.13/0.99    inference(flattening,[],[f22])).
% 2.13/0.99  
% 2.13/0.99  fof(f29,plain,(
% 2.13/0.99    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_tarski(k1_funct_1(sK3,sK1)) != k2_relset_1(k1_tarski(sK1),sK2,sK3) & k1_xboole_0 != sK2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK3,k1_tarski(sK1),sK2) & v1_funct_1(sK3))),
% 2.13/0.99    introduced(choice_axiom,[])).
% 2.13/0.99  
% 2.13/0.99  fof(f30,plain,(
% 2.13/0.99    k1_tarski(k1_funct_1(sK3,sK1)) != k2_relset_1(k1_tarski(sK1),sK2,sK3) & k1_xboole_0 != sK2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK3,k1_tarski(sK1),sK2) & v1_funct_1(sK3)),
% 2.13/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f23,f29])).
% 2.13/0.99  
% 2.13/0.99  fof(f50,plain,(
% 2.13/0.99    v1_funct_2(sK3,k1_tarski(sK1),sK2)),
% 2.13/0.99    inference(cnf_transformation,[],[f30])).
% 2.13/0.99  
% 2.13/0.99  fof(f2,axiom,(
% 2.13/0.99    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 2.13/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.13/0.99  
% 2.13/0.99  fof(f35,plain,(
% 2.13/0.99    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 2.13/0.99    inference(cnf_transformation,[],[f2])).
% 2.13/0.99  
% 2.13/0.99  fof(f3,axiom,(
% 2.13/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.13/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.13/0.99  
% 2.13/0.99  fof(f36,plain,(
% 2.13/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.13/0.99    inference(cnf_transformation,[],[f3])).
% 2.13/0.99  
% 2.13/0.99  fof(f54,plain,(
% 2.13/0.99    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 2.13/0.99    inference(definition_unfolding,[],[f35,f36])).
% 2.13/0.99  
% 2.13/0.99  fof(f63,plain,(
% 2.13/0.99    v1_funct_2(sK3,k1_enumset1(sK1,sK1,sK1),sK2)),
% 2.13/0.99    inference(definition_unfolding,[],[f50,f54])).
% 2.13/0.99  
% 2.13/0.99  fof(f10,axiom,(
% 2.13/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.13/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.13/0.99  
% 2.13/0.99  fof(f20,plain,(
% 2.13/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.13/0.99    inference(ennf_transformation,[],[f10])).
% 2.13/0.99  
% 2.13/0.99  fof(f21,plain,(
% 2.13/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.13/0.99    inference(flattening,[],[f20])).
% 2.13/0.99  
% 2.13/0.99  fof(f28,plain,(
% 2.13/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.13/0.99    inference(nnf_transformation,[],[f21])).
% 2.13/0.99  
% 2.13/0.99  fof(f43,plain,(
% 2.13/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.13/0.99    inference(cnf_transformation,[],[f28])).
% 2.13/0.99  
% 2.13/0.99  fof(f51,plain,(
% 2.13/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))),
% 2.13/0.99    inference(cnf_transformation,[],[f30])).
% 2.13/0.99  
% 2.13/0.99  fof(f62,plain,(
% 2.13/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)))),
% 2.13/0.99    inference(definition_unfolding,[],[f51,f54])).
% 2.13/0.99  
% 2.13/0.99  fof(f52,plain,(
% 2.13/0.99    k1_xboole_0 != sK2),
% 2.13/0.99    inference(cnf_transformation,[],[f30])).
% 2.13/0.99  
% 2.13/0.99  fof(f8,axiom,(
% 2.13/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.13/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.13/0.99  
% 2.13/0.99  fof(f18,plain,(
% 2.13/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.13/0.99    inference(ennf_transformation,[],[f8])).
% 2.13/0.99  
% 2.13/0.99  fof(f41,plain,(
% 2.13/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.13/0.99    inference(cnf_transformation,[],[f18])).
% 2.13/0.99  
% 2.13/0.99  fof(f1,axiom,(
% 2.13/0.99    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.13/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.13/0.99  
% 2.13/0.99  fof(f24,plain,(
% 2.13/0.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.13/0.99    inference(nnf_transformation,[],[f1])).
% 2.13/0.99  
% 2.13/0.99  fof(f25,plain,(
% 2.13/0.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.13/0.99    inference(rectify,[],[f24])).
% 2.13/0.99  
% 2.13/0.99  fof(f26,plain,(
% 2.13/0.99    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1))))),
% 2.13/0.99    introduced(choice_axiom,[])).
% 2.13/0.99  
% 2.13/0.99  fof(f27,plain,(
% 2.13/0.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.13/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 2.13/0.99  
% 2.13/0.99  fof(f32,plain,(
% 2.13/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 2.13/0.99    inference(cnf_transformation,[],[f27])).
% 2.13/0.99  
% 2.13/0.99  fof(f57,plain,(
% 2.13/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_enumset1(X0,X0,X0) != X1) )),
% 2.13/0.99    inference(definition_unfolding,[],[f32,f54])).
% 2.13/0.99  
% 2.13/0.99  fof(f64,plain,(
% 2.13/0.99    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_enumset1(X3,X3,X3) != X1) )),
% 2.13/0.99    inference(equality_resolution,[],[f57])).
% 2.13/0.99  
% 2.13/0.99  fof(f65,plain,(
% 2.13/0.99    ( ! [X3] : (r2_hidden(X3,k1_enumset1(X3,X3,X3))) )),
% 2.13/0.99    inference(equality_resolution,[],[f64])).
% 2.13/0.99  
% 2.13/0.99  fof(f7,axiom,(
% 2.13/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.13/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.13/0.99  
% 2.13/0.99  fof(f17,plain,(
% 2.13/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.13/0.99    inference(ennf_transformation,[],[f7])).
% 2.13/0.99  
% 2.13/0.99  fof(f40,plain,(
% 2.13/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.13/0.99    inference(cnf_transformation,[],[f17])).
% 2.13/0.99  
% 2.13/0.99  fof(f6,axiom,(
% 2.13/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)))),
% 2.13/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.13/0.99  
% 2.13/0.99  fof(f15,plain,(
% 2.13/0.99    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.13/0.99    inference(ennf_transformation,[],[f6])).
% 2.13/0.99  
% 2.13/0.99  fof(f16,plain,(
% 2.13/0.99    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.13/0.99    inference(flattening,[],[f15])).
% 2.13/0.99  
% 2.13/0.99  fof(f39,plain,(
% 2.13/0.99    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.13/0.99    inference(cnf_transformation,[],[f16])).
% 2.13/0.99  
% 2.13/0.99  fof(f60,plain,(
% 2.13/0.99    ( ! [X0,X1] : (k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.13/0.99    inference(definition_unfolding,[],[f39,f54])).
% 2.13/0.99  
% 2.13/0.99  fof(f49,plain,(
% 2.13/0.99    v1_funct_1(sK3)),
% 2.13/0.99    inference(cnf_transformation,[],[f30])).
% 2.13/0.99  
% 2.13/0.99  fof(f4,axiom,(
% 2.13/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 2.13/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.13/0.99  
% 2.13/0.99  fof(f13,plain,(
% 2.13/0.99    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 2.13/0.99    inference(ennf_transformation,[],[f4])).
% 2.13/0.99  
% 2.13/0.99  fof(f37,plain,(
% 2.13/0.99    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 2.13/0.99    inference(cnf_transformation,[],[f13])).
% 2.13/0.99  
% 2.13/0.99  fof(f59,plain,(
% 2.13/0.99    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_enumset1(X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 2.13/0.99    inference(definition_unfolding,[],[f37,f54])).
% 2.13/0.99  
% 2.13/0.99  fof(f5,axiom,(
% 2.13/0.99    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 2.13/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.13/0.99  
% 2.13/0.99  fof(f14,plain,(
% 2.13/0.99    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 2.13/0.99    inference(ennf_transformation,[],[f5])).
% 2.13/0.99  
% 2.13/0.99  fof(f38,plain,(
% 2.13/0.99    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.13/0.99    inference(cnf_transformation,[],[f14])).
% 2.13/0.99  
% 2.13/0.99  fof(f9,axiom,(
% 2.13/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.13/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.13/0.99  
% 2.13/0.99  fof(f19,plain,(
% 2.13/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.13/0.99    inference(ennf_transformation,[],[f9])).
% 2.13/0.99  
% 2.13/0.99  fof(f42,plain,(
% 2.13/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.13/0.99    inference(cnf_transformation,[],[f19])).
% 2.13/0.99  
% 2.13/0.99  fof(f53,plain,(
% 2.13/0.99    k1_tarski(k1_funct_1(sK3,sK1)) != k2_relset_1(k1_tarski(sK1),sK2,sK3)),
% 2.13/0.99    inference(cnf_transformation,[],[f30])).
% 2.13/0.99  
% 2.13/0.99  fof(f61,plain,(
% 2.13/0.99    k1_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK3)),
% 2.13/0.99    inference(definition_unfolding,[],[f53,f54,f54])).
% 2.13/0.99  
% 2.13/0.99  cnf(c_19,negated_conjecture,
% 2.13/0.99      ( v1_funct_2(sK3,k1_enumset1(sK1,sK1,sK1),sK2) ),
% 2.13/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_15,plain,
% 2.13/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.13/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.13/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.13/0.99      | k1_xboole_0 = X2 ),
% 2.13/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_18,negated_conjecture,
% 2.13/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))) ),
% 2.13/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_370,plain,
% 2.13/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.13/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.13/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 2.13/0.99      | sK3 != X0
% 2.13/0.99      | k1_xboole_0 = X2 ),
% 2.13/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_18]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_371,plain,
% 2.13/0.99      ( ~ v1_funct_2(sK3,X0,X1)
% 2.13/0.99      | k1_relset_1(X0,X1,sK3) = X0
% 2.13/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.13/0.99      | k1_xboole_0 = X1 ),
% 2.13/0.99      inference(unflattening,[status(thm)],[c_370]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_657,plain,
% 2.13/0.99      ( k1_relset_1(X0,X1,sK3) = X0
% 2.13/0.99      | k1_enumset1(sK1,sK1,sK1) != X0
% 2.13/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.13/0.99      | sK2 != X1
% 2.13/0.99      | sK3 != sK3
% 2.13/0.99      | k1_xboole_0 = X1 ),
% 2.13/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_371]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_658,plain,
% 2.13/0.99      ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK3) = k1_enumset1(sK1,sK1,sK1)
% 2.13/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))
% 2.13/0.99      | k1_xboole_0 = sK2 ),
% 2.13/0.99      inference(unflattening,[status(thm)],[c_657]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_17,negated_conjecture,
% 2.13/0.99      ( k1_xboole_0 != sK2 ),
% 2.13/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_659,plain,
% 2.13/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))
% 2.13/0.99      | k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK3) = k1_enumset1(sK1,sK1,sK1) ),
% 2.13/0.99      inference(global_propositional_subsumption,
% 2.13/0.99                [status(thm)],
% 2.13/0.99                [c_658,c_17]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_660,plain,
% 2.13/0.99      ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK3) = k1_enumset1(sK1,sK1,sK1)
% 2.13/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
% 2.13/0.99      inference(renaming,[status(thm)],[c_659]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_714,plain,
% 2.13/0.99      ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK3) = k1_enumset1(sK1,sK1,sK1) ),
% 2.13/0.99      inference(equality_resolution_simp,[status(thm)],[c_660]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_8,plain,
% 2.13/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.13/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.13/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_415,plain,
% 2.13/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.13/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.13/0.99      | sK3 != X2 ),
% 2.13/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_18]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_416,plain,
% 2.13/0.99      ( k1_relset_1(X0,X1,sK3) = k1_relat_1(sK3)
% 2.13/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.13/0.99      inference(unflattening,[status(thm)],[c_415]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1158,plain,
% 2.13/0.99      ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK3) = k1_relat_1(sK3) ),
% 2.13/0.99      inference(equality_resolution,[status(thm)],[c_416]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1402,plain,
% 2.13/0.99      ( k1_enumset1(sK1,sK1,sK1) = k1_relat_1(sK3) ),
% 2.13/0.99      inference(light_normalisation,[status(thm)],[c_714,c_1158]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_2,plain,
% 2.13/0.99      ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) ),
% 2.13/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1023,plain,
% 2.13/0.99      ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) = iProver_top ),
% 2.13/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1429,plain,
% 2.13/0.99      ( r2_hidden(sK1,k1_relat_1(sK3)) = iProver_top ),
% 2.13/0.99      inference(superposition,[status(thm)],[c_1402,c_1023]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_7,plain,
% 2.13/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.13/0.99      | v1_relat_1(X0) ),
% 2.13/0.99      inference(cnf_transformation,[],[f40]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_424,plain,
% 2.13/0.99      ( v1_relat_1(X0)
% 2.13/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 2.13/0.99      | sK3 != X0 ),
% 2.13/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_18]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_425,plain,
% 2.13/0.99      ( v1_relat_1(sK3)
% 2.13/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.13/0.99      inference(unflattening,[status(thm)],[c_424]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_6,plain,
% 2.13/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.13/0.99      | ~ v1_funct_1(X1)
% 2.13/0.99      | ~ v1_relat_1(X1)
% 2.13/0.99      | k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ),
% 2.13/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_20,negated_conjecture,
% 2.13/0.99      ( v1_funct_1(sK3) ),
% 2.13/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_225,plain,
% 2.13/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.13/0.99      | ~ v1_relat_1(X1)
% 2.13/0.99      | k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
% 2.13/0.99      | sK3 != X1 ),
% 2.13/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_20]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_226,plain,
% 2.13/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 2.13/0.99      | ~ v1_relat_1(sK3)
% 2.13/0.99      | k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0) ),
% 2.13/0.99      inference(unflattening,[status(thm)],[c_225]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_536,plain,
% 2.13/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 2.13/0.99      | k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
% 2.13/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
% 2.13/0.99      inference(resolution,[status(thm)],[c_425,c_226]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_829,plain,
% 2.13/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 2.13/0.99      | k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
% 2.13/0.99      | ~ sP2_iProver_split ),
% 2.13/0.99      inference(splitting,
% 2.13/0.99                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 2.13/0.99                [c_536]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1020,plain,
% 2.13/0.99      ( k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
% 2.13/0.99      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 2.13/0.99      | sP2_iProver_split != iProver_top ),
% 2.13/0.99      inference(predicate_to_equality,[status(thm)],[c_829]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_830,plain,
% 2.13/0.99      ( sP2_iProver_split | sP0_iProver_split ),
% 2.13/0.99      inference(splitting,
% 2.13/0.99                [splitting(split),new_symbols(definition,[])],
% 2.13/0.99                [c_536]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_865,plain,
% 2.13/0.99      ( sP2_iProver_split = iProver_top
% 2.13/0.99      | sP0_iProver_split = iProver_top ),
% 2.13/0.99      inference(predicate_to_equality,[status(thm)],[c_830]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_866,plain,
% 2.13/0.99      ( k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
% 2.13/0.99      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 2.13/0.99      | sP2_iProver_split != iProver_top ),
% 2.13/0.99      inference(predicate_to_equality,[status(thm)],[c_829]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_832,plain,( X0 = X0 ),theory(equality) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1119,plain,
% 2.13/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) = k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
% 2.13/0.99      inference(instantiation,[status(thm)],[c_832]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_4,plain,
% 2.13/0.99      ( ~ v1_relat_1(X0)
% 2.13/0.99      | k9_relat_1(X0,k1_enumset1(X1,X1,X1)) = k11_relat_1(X0,X1) ),
% 2.13/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_559,plain,
% 2.13/0.99      ( k9_relat_1(X0,k1_enumset1(X1,X1,X1)) = k11_relat_1(X0,X1)
% 2.13/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
% 2.13/0.99      | sK3 != X0 ),
% 2.13/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_425]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_560,plain,
% 2.13/0.99      ( k9_relat_1(sK3,k1_enumset1(X0,X0,X0)) = k11_relat_1(sK3,X0)
% 2.13/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
% 2.13/0.99      inference(unflattening,[status(thm)],[c_559]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_826,plain,
% 2.13/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.13/0.99      | ~ sP0_iProver_split ),
% 2.13/0.99      inference(splitting,
% 2.13/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.13/0.99                [c_560]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1120,plain,
% 2.13/0.99      ( ~ sP0_iProver_split
% 2.13/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
% 2.13/0.99      inference(instantiation,[status(thm)],[c_826]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1124,plain,
% 2.13/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))
% 2.13/0.99      | sP0_iProver_split != iProver_top ),
% 2.13/0.99      inference(predicate_to_equality,[status(thm)],[c_1120]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_2171,plain,
% 2.13/0.99      ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 2.13/0.99      | k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0) ),
% 2.13/0.99      inference(global_propositional_subsumption,
% 2.13/0.99                [status(thm)],
% 2.13/0.99                [c_1020,c_865,c_866,c_1119,c_1124]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_2172,plain,
% 2.13/0.99      ( k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
% 2.13/0.99      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top ),
% 2.13/0.99      inference(renaming,[status(thm)],[c_2171]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_2180,plain,
% 2.13/0.99      ( k1_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) = k11_relat_1(sK3,sK1) ),
% 2.13/0.99      inference(superposition,[status(thm)],[c_1429,c_2172]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_827,plain,
% 2.13/0.99      ( k9_relat_1(sK3,k1_enumset1(X0,X0,X0)) = k11_relat_1(sK3,X0)
% 2.13/0.99      | ~ sP1_iProver_split ),
% 2.13/0.99      inference(splitting,
% 2.13/0.99                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 2.13/0.99                [c_560]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1017,plain,
% 2.13/0.99      ( k9_relat_1(sK3,k1_enumset1(X0,X0,X0)) = k11_relat_1(sK3,X0)
% 2.13/0.99      | sP1_iProver_split != iProver_top ),
% 2.13/0.99      inference(predicate_to_equality,[status(thm)],[c_827]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_828,plain,
% 2.13/0.99      ( sP1_iProver_split | sP0_iProver_split ),
% 2.13/0.99      inference(splitting,
% 2.13/0.99                [splitting(split),new_symbols(definition,[])],
% 2.13/0.99                [c_560]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1790,plain,
% 2.13/0.99      ( k9_relat_1(sK3,k1_enumset1(X0,X0,X0)) = k11_relat_1(sK3,X0) ),
% 2.13/0.99      inference(global_propositional_subsumption,
% 2.13/0.99                [status(thm)],
% 2.13/0.99                [c_1017,c_828,c_827,c_1119,c_1120]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1794,plain,
% 2.13/0.99      ( k9_relat_1(sK3,k1_relat_1(sK3)) = k11_relat_1(sK3,sK1) ),
% 2.13/0.99      inference(superposition,[status(thm)],[c_1402,c_1790]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_5,plain,
% 2.13/0.99      ( ~ v1_relat_1(X0)
% 2.13/0.99      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 2.13/0.99      inference(cnf_transformation,[],[f38]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_550,plain,
% 2.13/0.99      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 2.13/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 2.13/0.99      | sK3 != X0 ),
% 2.13/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_425]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_551,plain,
% 2.13/0.99      ( k9_relat_1(sK3,k1_relat_1(sK3)) = k2_relat_1(sK3)
% 2.13/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.13/0.99      inference(unflattening,[status(thm)],[c_550]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1121,plain,
% 2.13/0.99      ( k9_relat_1(sK3,k1_relat_1(sK3)) = k2_relat_1(sK3)
% 2.13/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
% 2.13/0.99      inference(instantiation,[status(thm)],[c_551]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1248,plain,
% 2.13/0.99      ( k9_relat_1(sK3,k1_relat_1(sK3)) = k2_relat_1(sK3) ),
% 2.13/0.99      inference(global_propositional_subsumption,
% 2.13/0.99                [status(thm)],
% 2.13/0.99                [c_551,c_1119,c_1121]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1795,plain,
% 2.13/0.99      ( k11_relat_1(sK3,sK1) = k2_relat_1(sK3) ),
% 2.13/0.99      inference(light_normalisation,[status(thm)],[c_1794,c_1248]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_2182,plain,
% 2.13/0.99      ( k1_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) = k2_relat_1(sK3) ),
% 2.13/0.99      inference(light_normalisation,[status(thm)],[c_2180,c_1795]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_833,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1145,plain,
% 2.13/0.99      ( k2_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK3) != X0
% 2.13/0.99      | k1_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != X0
% 2.13/0.99      | k1_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) = k2_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK3) ),
% 2.13/0.99      inference(instantiation,[status(thm)],[c_833]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1201,plain,
% 2.13/0.99      ( k2_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK3) != k2_relat_1(sK3)
% 2.13/0.99      | k1_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) = k2_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK3)
% 2.13/0.99      | k1_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relat_1(sK3) ),
% 2.13/0.99      inference(instantiation,[status(thm)],[c_1145]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_9,plain,
% 2.13/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.13/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.13/0.99      inference(cnf_transformation,[],[f42]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_406,plain,
% 2.13/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.13/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.13/0.99      | sK3 != X2 ),
% 2.13/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_18]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_407,plain,
% 2.13/0.99      ( k2_relset_1(X0,X1,sK3) = k2_relat_1(sK3)
% 2.13/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.13/0.99      inference(unflattening,[status(thm)],[c_406]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1123,plain,
% 2.13/0.99      ( k2_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK3) = k2_relat_1(sK3)
% 2.13/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
% 2.13/0.99      inference(instantiation,[status(thm)],[c_407]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_16,negated_conjecture,
% 2.13/0.99      ( k1_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK3) ),
% 2.13/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(contradiction,plain,
% 2.13/0.99      ( $false ),
% 2.13/0.99      inference(minisat,[status(thm)],[c_2182,c_1201,c_1123,c_1119,c_16]) ).
% 2.13/0.99  
% 2.13/0.99  
% 2.13/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.13/0.99  
% 2.13/0.99  ------                               Statistics
% 2.13/0.99  
% 2.13/0.99  ------ General
% 2.13/0.99  
% 2.13/0.99  abstr_ref_over_cycles:                  0
% 2.13/0.99  abstr_ref_under_cycles:                 0
% 2.13/0.99  gc_basic_clause_elim:                   0
% 2.13/0.99  forced_gc_time:                         0
% 2.13/0.99  parsing_time:                           0.008
% 2.13/0.99  unif_index_cands_time:                  0.
% 2.13/0.99  unif_index_add_time:                    0.
% 2.13/0.99  orderings_time:                         0.
% 2.13/0.99  out_proof_time:                         0.011
% 2.13/0.99  total_time:                             0.103
% 2.13/0.99  num_of_symbols:                         54
% 2.13/0.99  num_of_terms:                           2229
% 2.13/0.99  
% 2.13/0.99  ------ Preprocessing
% 2.13/0.99  
% 2.13/0.99  num_of_splits:                          4
% 2.13/0.99  num_of_split_atoms:                     3
% 2.13/0.99  num_of_reused_defs:                     1
% 2.13/0.99  num_eq_ax_congr_red:                    16
% 2.13/0.99  num_of_sem_filtered_clauses:            1
% 2.13/0.99  num_of_subtypes:                        0
% 2.13/0.99  monotx_restored_types:                  0
% 2.13/0.99  sat_num_of_epr_types:                   0
% 2.13/0.99  sat_num_of_non_cyclic_types:            0
% 2.13/0.99  sat_guarded_non_collapsed_types:        0
% 2.13/0.99  num_pure_diseq_elim:                    0
% 2.13/0.99  simp_replaced_by:                       0
% 2.13/0.99  res_preprocessed:                       96
% 2.13/0.99  prep_upred:                             0
% 2.13/0.99  prep_unflattend:                        50
% 2.13/0.99  smt_new_axioms:                         0
% 2.13/0.99  pred_elim_cands:                        1
% 2.13/0.99  pred_elim:                              4
% 2.13/0.99  pred_elim_cl:                           7
% 2.13/0.99  pred_elim_cycles:                       9
% 2.13/0.99  merged_defs:                            0
% 2.13/0.99  merged_defs_ncl:                        0
% 2.13/0.99  bin_hyper_res:                          0
% 2.13/0.99  prep_cycles:                            4
% 2.13/0.99  pred_elim_time:                         0.011
% 2.13/0.99  splitting_time:                         0.
% 2.13/0.99  sem_filter_time:                        0.
% 2.13/0.99  monotx_time:                            0.
% 2.13/0.99  subtype_inf_time:                       0.
% 2.13/0.99  
% 2.13/0.99  ------ Problem properties
% 2.13/0.99  
% 2.13/0.99  clauses:                                18
% 2.13/0.99  conjectures:                            2
% 2.13/0.99  epr:                                    3
% 2.13/0.99  horn:                                   14
% 2.13/0.99  ground:                                 7
% 2.13/0.99  unary:                                  4
% 2.13/0.99  binary:                                 9
% 2.13/0.99  lits:                                   38
% 2.13/0.99  lits_eq:                                25
% 2.13/0.99  fd_pure:                                0
% 2.13/0.99  fd_pseudo:                              0
% 2.13/0.99  fd_cond:                                0
% 2.13/0.99  fd_pseudo_cond:                         2
% 2.13/0.99  ac_symbols:                             0
% 2.13/0.99  
% 2.13/0.99  ------ Propositional Solver
% 2.13/0.99  
% 2.13/0.99  prop_solver_calls:                      26
% 2.13/0.99  prop_fast_solver_calls:                 617
% 2.13/0.99  smt_solver_calls:                       0
% 2.13/0.99  smt_fast_solver_calls:                  0
% 2.13/0.99  prop_num_of_clauses:                    736
% 2.13/0.99  prop_preprocess_simplified:             2897
% 2.13/0.99  prop_fo_subsumed:                       8
% 2.13/0.99  prop_solver_time:                       0.
% 2.13/0.99  smt_solver_time:                        0.
% 2.13/0.99  smt_fast_solver_time:                   0.
% 2.13/0.99  prop_fast_solver_time:                  0.
% 2.13/0.99  prop_unsat_core_time:                   0.
% 2.13/0.99  
% 2.13/0.99  ------ QBF
% 2.13/0.99  
% 2.13/0.99  qbf_q_res:                              0
% 2.13/0.99  qbf_num_tautologies:                    0
% 2.13/0.99  qbf_prep_cycles:                        0
% 2.13/0.99  
% 2.13/0.99  ------ BMC1
% 2.13/0.99  
% 2.13/0.99  bmc1_current_bound:                     -1
% 2.13/0.99  bmc1_last_solved_bound:                 -1
% 2.13/0.99  bmc1_unsat_core_size:                   -1
% 2.13/0.99  bmc1_unsat_core_parents_size:           -1
% 2.13/0.99  bmc1_merge_next_fun:                    0
% 2.13/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.13/0.99  
% 2.13/0.99  ------ Instantiation
% 2.13/0.99  
% 2.13/0.99  inst_num_of_clauses:                    248
% 2.13/0.99  inst_num_in_passive:                    15
% 2.13/0.99  inst_num_in_active:                     126
% 2.13/0.99  inst_num_in_unprocessed:                107
% 2.13/0.99  inst_num_of_loops:                      140
% 2.13/0.99  inst_num_of_learning_restarts:          0
% 2.13/0.99  inst_num_moves_active_passive:          12
% 2.13/0.99  inst_lit_activity:                      0
% 2.13/0.99  inst_lit_activity_moves:                0
% 2.13/0.99  inst_num_tautologies:                   0
% 2.13/0.99  inst_num_prop_implied:                  0
% 2.13/0.99  inst_num_existing_simplified:           0
% 2.13/0.99  inst_num_eq_res_simplified:             0
% 2.13/0.99  inst_num_child_elim:                    0
% 2.13/0.99  inst_num_of_dismatching_blockings:      46
% 2.13/0.99  inst_num_of_non_proper_insts:           211
% 2.13/0.99  inst_num_of_duplicates:                 0
% 2.13/0.99  inst_inst_num_from_inst_to_res:         0
% 2.13/0.99  inst_dismatching_checking_time:         0.
% 2.13/0.99  
% 2.13/0.99  ------ Resolution
% 2.13/0.99  
% 2.13/0.99  res_num_of_clauses:                     0
% 2.13/0.99  res_num_in_passive:                     0
% 2.13/0.99  res_num_in_active:                      0
% 2.13/0.99  res_num_of_loops:                       100
% 2.13/0.99  res_forward_subset_subsumed:            41
% 2.13/0.99  res_backward_subset_subsumed:           0
% 2.13/0.99  res_forward_subsumed:                   0
% 2.13/0.99  res_backward_subsumed:                  0
% 2.13/0.99  res_forward_subsumption_resolution:     0
% 2.13/0.99  res_backward_subsumption_resolution:    0
% 2.13/0.99  res_clause_to_clause_subsumption:       58
% 2.13/0.99  res_orphan_elimination:                 0
% 2.13/0.99  res_tautology_del:                      24
% 2.13/0.99  res_num_eq_res_simplified:              1
% 2.13/0.99  res_num_sel_changes:                    0
% 2.13/0.99  res_moves_from_active_to_pass:          0
% 2.13/0.99  
% 2.13/0.99  ------ Superposition
% 2.13/0.99  
% 2.13/0.99  sup_time_total:                         0.
% 2.13/0.99  sup_time_generating:                    0.
% 2.13/0.99  sup_time_sim_full:                      0.
% 2.13/0.99  sup_time_sim_immed:                     0.
% 2.13/0.99  
% 2.13/0.99  sup_num_of_clauses:                     31
% 2.13/0.99  sup_num_in_active:                      22
% 2.13/0.99  sup_num_in_passive:                     9
% 2.13/0.99  sup_num_of_loops:                       27
% 2.13/0.99  sup_fw_superposition:                   6
% 2.13/0.99  sup_bw_superposition:                   7
% 2.13/0.99  sup_immediate_simplified:               3
% 2.13/0.99  sup_given_eliminated:                   0
% 2.13/0.99  comparisons_done:                       0
% 2.13/0.99  comparisons_avoided:                    8
% 2.13/0.99  
% 2.13/0.99  ------ Simplifications
% 2.13/0.99  
% 2.13/0.99  
% 2.13/0.99  sim_fw_subset_subsumed:                 0
% 2.13/0.99  sim_bw_subset_subsumed:                 0
% 2.13/0.99  sim_fw_subsumed:                        0
% 2.13/0.99  sim_bw_subsumed:                        0
% 2.13/0.99  sim_fw_subsumption_res:                 0
% 2.13/0.99  sim_bw_subsumption_res:                 0
% 2.13/0.99  sim_tautology_del:                      0
% 2.13/0.99  sim_eq_tautology_del:                   2
% 2.13/0.99  sim_eq_res_simp:                        0
% 2.13/0.99  sim_fw_demodulated:                     0
% 2.13/0.99  sim_bw_demodulated:                     6
% 2.13/0.99  sim_light_normalised:                   4
% 2.13/0.99  sim_joinable_taut:                      0
% 2.13/0.99  sim_joinable_simp:                      0
% 2.13/0.99  sim_ac_normalised:                      0
% 2.13/0.99  sim_smt_subsumption:                    0
% 2.13/0.99  
%------------------------------------------------------------------------------
