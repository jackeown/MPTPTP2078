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
% DateTime   : Thu Dec  3 12:05:22 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 659 expanded)
%              Number of clauses        :   82 ( 192 expanded)
%              Number of leaves         :   18 ( 151 expanded)
%              Depth                    :   22
%              Number of atoms          :  374 (1834 expanded)
%              Number of equality atoms :  194 ( 895 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f35,plain,
    ( ? [X0,X1,X2] :
        ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( k1_tarski(k1_funct_1(sK2,sK0)) != k2_relset_1(k1_tarski(sK0),sK1,sK2)
      & k1_xboole_0 != sK1
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_2(sK2,k1_tarski(sK0),sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( k1_tarski(k1_funct_1(sK2,sK0)) != k2_relset_1(k1_tarski(sK0),sK1,sK2)
    & k1_xboole_0 != sK1
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_2(sK2,k1_tarski(sK0),sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f35])).

fof(f61,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f38,f39])).

fof(f65,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f37,f64])).

fof(f72,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f61,f65])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f60,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f73,plain,(
    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f60,f65])).

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
    inference(ennf_transformation,[],[f14])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f62,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f36])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f31])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f41,f64])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f49,f65])).

fof(f59,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f44,f65])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f48,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f63,plain,(
    k1_tarski(k1_funct_1(sK2,sK0)) != k2_relset_1(k1_tarski(sK0),sK1,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f71,plain,(
    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) ),
    inference(definition_unfolding,[],[f63,f65,f65])).

cnf(c_10,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_6,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_276,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_10,c_6])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_373,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_276,c_21])).

cnf(c_374,plain,
    ( r1_tarski(k1_relat_1(sK2),X0)
    | ~ v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_373])).

cnf(c_811,plain,
    ( r1_tarski(k1_relat_1(sK2),X0_49)
    | ~ v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)) ),
    inference(subtyping,[status(esa)],[c_374])).

cnf(c_1055,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))
    | r1_tarski(k1_relat_1(sK2),X0_49) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_811])).

cnf(c_878,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))
    | r1_tarski(k1_relat_1(sK2),X0_49) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_811])).

cnf(c_825,plain,
    ( X0_51 = X0_51 ),
    theory(equality)).

cnf(c_1154,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) = k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_825])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_358,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_21])).

cnf(c_359,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_358])).

cnf(c_812,plain,
    ( ~ v1_relat_1(X0_49)
    | v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_359])).

cnf(c_1149,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(X0_49,X1_49))
    | v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)) ),
    inference(instantiation,[status(thm)],[c_812])).

cnf(c_1218,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_1149])).

cnf(c_1219,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1218])).

cnf(c_7,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_817,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_49,X1_49)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1297,plain,
    ( v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_817])).

cnf(c_1298,plain,
    ( v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1297])).

cnf(c_1537,plain,
    ( r1_tarski(k1_relat_1(sK2),X0_49) = iProver_top
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1055,c_878,c_1154,c_1219,c_1298])).

cnf(c_1538,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))
    | r1_tarski(k1_relat_1(sK2),X0_49) = iProver_top ),
    inference(renaming,[status(thm)],[c_1537])).

cnf(c_22,negated_conjecture,
    ( v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_388,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_21])).

cnf(c_389,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | k1_relset_1(X0,X1,sK2) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_388])).

cnf(c_618,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != X0
    | k1_relset_1(X0,X1,sK2) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK1 != X1
    | sK2 != sK2
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_389])).

cnf(c_619,plain,
    ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_618])).

cnf(c_20,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_620,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_619,c_20])).

cnf(c_621,plain,
    ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    inference(renaming,[status(thm)],[c_620])).

cnf(c_679,plain,
    ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(equality_resolution_simp,[status(thm)],[c_621])).

cnf(c_806,plain,
    ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(subtyping,[status(esa)],[c_679])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_433,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_21])).

cnf(c_434,plain,
    ( k1_relset_1(X0,X1,sK2) = k1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_433])).

cnf(c_809,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))
    | k1_relset_1(X0_49,X1_49,sK2) = k1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_434])).

cnf(c_1177,plain,
    ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k1_relat_1(sK2) ),
    inference(equality_resolution,[status(thm)],[c_809])).

cnf(c_1241,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_806,c_1177])).

cnf(c_1543,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))
    | r1_tarski(k1_relat_1(sK2),X0_49) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1538,c_1241])).

cnf(c_1549,plain,
    ( r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1543])).

cnf(c_1,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k2_enumset1(X2,X2,X2,X0),X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_820,plain,
    ( r2_hidden(X0_50,X0_49)
    | ~ r1_tarski(k2_enumset1(X1_50,X1_50,X1_50,X0_50),X0_49) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1048,plain,
    ( r2_hidden(X0_50,X0_49) = iProver_top
    | r1_tarski(k2_enumset1(X1_50,X1_50,X1_50,X0_50),X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_820])).

cnf(c_1314,plain,
    ( r2_hidden(sK0,X0_49) = iProver_top
    | r1_tarski(k1_relat_1(sK2),X0_49) != iProver_top ),
    inference(superposition,[status(thm)],[c_1241,c_1048])).

cnf(c_1891,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1549,c_1314])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_257,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_23])).

cnf(c_258,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | k2_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)) = k11_relat_1(sK2,X0) ),
    inference(unflattening,[status(thm)],[c_257])).

cnf(c_813,plain,
    ( ~ r2_hidden(X0_50,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | k2_enumset1(k1_funct_1(sK2,X0_50),k1_funct_1(sK2,X0_50),k1_funct_1(sK2,X0_50),k1_funct_1(sK2,X0_50)) = k11_relat_1(sK2,X0_50) ),
    inference(subtyping,[status(esa)],[c_258])).

cnf(c_1053,plain,
    ( k2_enumset1(k1_funct_1(sK2,X0_50),k1_funct_1(sK2,X0_50),k1_funct_1(sK2,X0_50),k1_funct_1(sK2,X0_50)) = k11_relat_1(sK2,X0_50)
    | r2_hidden(X0_50,k1_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_813])).

cnf(c_872,plain,
    ( k2_enumset1(k1_funct_1(sK2,X0_50),k1_funct_1(sK2,X0_50),k1_funct_1(sK2,X0_50),k1_funct_1(sK2,X0_50)) = k11_relat_1(sK2,X0_50)
    | r2_hidden(X0_50,k1_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_813])).

cnf(c_1552,plain,
    ( r2_hidden(X0_50,k1_relat_1(sK2)) != iProver_top
    | k2_enumset1(k1_funct_1(sK2,X0_50),k1_funct_1(sK2,X0_50),k1_funct_1(sK2,X0_50),k1_funct_1(sK2,X0_50)) = k11_relat_1(sK2,X0_50) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1053,c_872,c_1154,c_1219,c_1298])).

cnf(c_1553,plain,
    ( k2_enumset1(k1_funct_1(sK2,X0_50),k1_funct_1(sK2,X0_50),k1_funct_1(sK2,X0_50),k1_funct_1(sK2,X0_50)) = k11_relat_1(sK2,X0_50)
    | r2_hidden(X0_50,k1_relat_1(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1552])).

cnf(c_1960,plain,
    ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k11_relat_1(sK2,sK0) ),
    inference(superposition,[status(thm)],[c_1891,c_1553])).

cnf(c_1054,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(X0_49)
    | v1_relat_1(X0_49) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_812])).

cnf(c_1477,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1054,c_1154,c_1219,c_1298])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_818,plain,
    ( ~ v1_relat_1(X0_49)
    | k9_relat_1(X0_49,k2_enumset1(X0_50,X0_50,X0_50,X0_50)) = k11_relat_1(X0_49,X0_50) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1050,plain,
    ( k9_relat_1(X0_49,k2_enumset1(X0_50,X0_50,X0_50,X0_50)) = k11_relat_1(X0_49,X0_50)
    | v1_relat_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_818])).

cnf(c_1672,plain,
    ( k9_relat_1(sK2,k2_enumset1(X0_50,X0_50,X0_50,X0_50)) = k11_relat_1(sK2,X0_50) ),
    inference(superposition,[status(thm)],[c_1477,c_1050])).

cnf(c_1681,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) = k11_relat_1(sK2,sK0) ),
    inference(superposition,[status(thm)],[c_1241,c_1672])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_816,plain,
    ( ~ v1_relat_1(X0_49)
    | k9_relat_1(X0_49,k1_relat_1(X0_49)) = k2_relat_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1052,plain,
    ( k9_relat_1(X0_49,k1_relat_1(X0_49)) = k2_relat_1(X0_49)
    | v1_relat_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_816])).

cnf(c_1482,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1477,c_1052])).

cnf(c_1682,plain,
    ( k11_relat_1(sK2,sK0) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1681,c_1482])).

cnf(c_1961,plain,
    ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1960,c_1682])).

cnf(c_826,plain,
    ( X0_49 != X1_49
    | X2_49 != X1_49
    | X2_49 = X0_49 ),
    theory(equality)).

cnf(c_1173,plain,
    ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != X0_49
    | k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)
    | k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != X0_49 ),
    inference(instantiation,[status(thm)],[c_826])).

cnf(c_1203,plain,
    ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)
    | k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relat_1(sK2)
    | k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1173])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_424,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_21])).

cnf(c_425,plain,
    ( k2_relset_1(X0,X1,sK2) = k2_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_424])).

cnf(c_810,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))
    | k2_relset_1(X0_49,X1_49,sK2) = k2_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_425])).

cnf(c_1155,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_810])).

cnf(c_19,negated_conjecture,
    ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_815,negated_conjecture,
    ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1961,c_1203,c_1155,c_1154,c_815])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:37:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.66/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/0.98  
% 1.66/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.66/0.98  
% 1.66/0.98  ------  iProver source info
% 1.66/0.98  
% 1.66/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.66/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.66/0.98  git: non_committed_changes: false
% 1.66/0.98  git: last_make_outside_of_git: false
% 1.66/0.98  
% 1.66/0.98  ------ 
% 1.66/0.98  
% 1.66/0.98  ------ Input Options
% 1.66/0.98  
% 1.66/0.98  --out_options                           all
% 1.66/0.98  --tptp_safe_out                         true
% 1.66/0.98  --problem_path                          ""
% 1.66/0.98  --include_path                          ""
% 1.66/0.98  --clausifier                            res/vclausify_rel
% 1.66/0.98  --clausifier_options                    --mode clausify
% 1.66/0.98  --stdin                                 false
% 1.66/0.98  --stats_out                             all
% 1.66/0.98  
% 1.66/0.98  ------ General Options
% 1.66/0.98  
% 1.66/0.98  --fof                                   false
% 1.66/0.98  --time_out_real                         305.
% 1.66/0.98  --time_out_virtual                      -1.
% 1.66/0.98  --symbol_type_check                     false
% 1.66/0.98  --clausify_out                          false
% 1.66/0.98  --sig_cnt_out                           false
% 1.66/0.98  --trig_cnt_out                          false
% 1.66/0.98  --trig_cnt_out_tolerance                1.
% 1.66/0.98  --trig_cnt_out_sk_spl                   false
% 1.66/0.98  --abstr_cl_out                          false
% 1.66/0.98  
% 1.66/0.98  ------ Global Options
% 1.66/0.98  
% 1.66/0.98  --schedule                              default
% 1.66/0.98  --add_important_lit                     false
% 1.66/0.98  --prop_solver_per_cl                    1000
% 1.66/0.98  --min_unsat_core                        false
% 1.66/0.98  --soft_assumptions                      false
% 1.66/0.98  --soft_lemma_size                       3
% 1.66/0.98  --prop_impl_unit_size                   0
% 1.66/0.98  --prop_impl_unit                        []
% 1.66/0.98  --share_sel_clauses                     true
% 1.66/0.98  --reset_solvers                         false
% 1.66/0.98  --bc_imp_inh                            [conj_cone]
% 1.66/0.98  --conj_cone_tolerance                   3.
% 1.66/0.98  --extra_neg_conj                        none
% 1.66/0.98  --large_theory_mode                     true
% 1.66/0.98  --prolific_symb_bound                   200
% 1.66/0.98  --lt_threshold                          2000
% 1.66/0.98  --clause_weak_htbl                      true
% 1.66/0.98  --gc_record_bc_elim                     false
% 1.66/0.98  
% 1.66/0.98  ------ Preprocessing Options
% 1.66/0.98  
% 1.66/0.98  --preprocessing_flag                    true
% 1.66/0.98  --time_out_prep_mult                    0.1
% 1.66/0.98  --splitting_mode                        input
% 1.66/0.98  --splitting_grd                         true
% 1.66/0.98  --splitting_cvd                         false
% 1.66/0.98  --splitting_cvd_svl                     false
% 1.66/0.98  --splitting_nvd                         32
% 1.66/0.98  --sub_typing                            true
% 1.66/0.98  --prep_gs_sim                           true
% 1.66/0.98  --prep_unflatten                        true
% 1.66/0.98  --prep_res_sim                          true
% 1.66/0.98  --prep_upred                            true
% 1.66/0.98  --prep_sem_filter                       exhaustive
% 1.66/0.98  --prep_sem_filter_out                   false
% 1.66/0.98  --pred_elim                             true
% 1.66/0.98  --res_sim_input                         true
% 1.66/0.98  --eq_ax_congr_red                       true
% 1.66/0.98  --pure_diseq_elim                       true
% 1.66/0.98  --brand_transform                       false
% 1.66/0.98  --non_eq_to_eq                          false
% 1.66/0.98  --prep_def_merge                        true
% 1.66/0.98  --prep_def_merge_prop_impl              false
% 1.66/0.98  --prep_def_merge_mbd                    true
% 1.66/0.98  --prep_def_merge_tr_red                 false
% 1.66/0.98  --prep_def_merge_tr_cl                  false
% 1.66/0.98  --smt_preprocessing                     true
% 1.66/0.98  --smt_ac_axioms                         fast
% 1.66/0.98  --preprocessed_out                      false
% 1.66/0.98  --preprocessed_stats                    false
% 1.66/0.98  
% 1.66/0.98  ------ Abstraction refinement Options
% 1.66/0.98  
% 1.66/0.98  --abstr_ref                             []
% 1.66/0.98  --abstr_ref_prep                        false
% 1.66/0.98  --abstr_ref_until_sat                   false
% 1.66/0.98  --abstr_ref_sig_restrict                funpre
% 1.66/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.66/0.98  --abstr_ref_under                       []
% 1.66/0.98  
% 1.66/0.98  ------ SAT Options
% 1.66/0.98  
% 1.66/0.98  --sat_mode                              false
% 1.66/0.98  --sat_fm_restart_options                ""
% 1.66/0.98  --sat_gr_def                            false
% 1.66/0.98  --sat_epr_types                         true
% 1.66/0.98  --sat_non_cyclic_types                  false
% 1.66/0.98  --sat_finite_models                     false
% 1.66/0.98  --sat_fm_lemmas                         false
% 1.66/0.98  --sat_fm_prep                           false
% 1.66/0.98  --sat_fm_uc_incr                        true
% 1.66/0.98  --sat_out_model                         small
% 1.66/0.98  --sat_out_clauses                       false
% 1.66/0.98  
% 1.66/0.98  ------ QBF Options
% 1.66/0.98  
% 1.66/0.98  --qbf_mode                              false
% 1.66/0.98  --qbf_elim_univ                         false
% 1.66/0.98  --qbf_dom_inst                          none
% 1.66/0.98  --qbf_dom_pre_inst                      false
% 1.66/0.98  --qbf_sk_in                             false
% 1.66/0.98  --qbf_pred_elim                         true
% 1.66/0.98  --qbf_split                             512
% 1.66/0.98  
% 1.66/0.98  ------ BMC1 Options
% 1.66/0.98  
% 1.66/0.98  --bmc1_incremental                      false
% 1.66/0.98  --bmc1_axioms                           reachable_all
% 1.66/0.98  --bmc1_min_bound                        0
% 1.66/0.98  --bmc1_max_bound                        -1
% 1.66/0.98  --bmc1_max_bound_default                -1
% 1.66/0.98  --bmc1_symbol_reachability              true
% 1.66/0.98  --bmc1_property_lemmas                  false
% 1.66/0.98  --bmc1_k_induction                      false
% 1.66/0.98  --bmc1_non_equiv_states                 false
% 1.66/0.98  --bmc1_deadlock                         false
% 1.66/0.98  --bmc1_ucm                              false
% 1.66/0.98  --bmc1_add_unsat_core                   none
% 1.66/0.98  --bmc1_unsat_core_children              false
% 1.66/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.66/0.98  --bmc1_out_stat                         full
% 1.66/0.98  --bmc1_ground_init                      false
% 1.66/0.98  --bmc1_pre_inst_next_state              false
% 1.66/0.98  --bmc1_pre_inst_state                   false
% 1.66/0.98  --bmc1_pre_inst_reach_state             false
% 1.66/0.98  --bmc1_out_unsat_core                   false
% 1.66/0.98  --bmc1_aig_witness_out                  false
% 1.66/0.98  --bmc1_verbose                          false
% 1.66/0.98  --bmc1_dump_clauses_tptp                false
% 1.66/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.66/0.98  --bmc1_dump_file                        -
% 1.66/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.66/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.66/0.98  --bmc1_ucm_extend_mode                  1
% 1.66/0.98  --bmc1_ucm_init_mode                    2
% 1.66/0.98  --bmc1_ucm_cone_mode                    none
% 1.66/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.66/0.98  --bmc1_ucm_relax_model                  4
% 1.66/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.66/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.66/0.98  --bmc1_ucm_layered_model                none
% 1.66/0.98  --bmc1_ucm_max_lemma_size               10
% 1.66/0.98  
% 1.66/0.98  ------ AIG Options
% 1.66/0.98  
% 1.66/0.98  --aig_mode                              false
% 1.66/0.98  
% 1.66/0.98  ------ Instantiation Options
% 1.66/0.98  
% 1.66/0.98  --instantiation_flag                    true
% 1.66/0.98  --inst_sos_flag                         false
% 1.66/0.98  --inst_sos_phase                        true
% 1.66/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.66/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.66/0.98  --inst_lit_sel_side                     num_symb
% 1.66/0.98  --inst_solver_per_active                1400
% 1.66/0.98  --inst_solver_calls_frac                1.
% 1.66/0.98  --inst_passive_queue_type               priority_queues
% 1.66/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.66/0.98  --inst_passive_queues_freq              [25;2]
% 1.66/0.98  --inst_dismatching                      true
% 1.66/0.98  --inst_eager_unprocessed_to_passive     true
% 1.66/0.98  --inst_prop_sim_given                   true
% 1.66/0.98  --inst_prop_sim_new                     false
% 1.66/0.98  --inst_subs_new                         false
% 1.66/0.98  --inst_eq_res_simp                      false
% 1.66/0.98  --inst_subs_given                       false
% 1.66/0.98  --inst_orphan_elimination               true
% 1.66/0.98  --inst_learning_loop_flag               true
% 1.66/0.98  --inst_learning_start                   3000
% 1.66/0.98  --inst_learning_factor                  2
% 1.66/0.98  --inst_start_prop_sim_after_learn       3
% 1.66/0.98  --inst_sel_renew                        solver
% 1.66/0.98  --inst_lit_activity_flag                true
% 1.66/0.98  --inst_restr_to_given                   false
% 1.66/0.98  --inst_activity_threshold               500
% 1.66/0.98  --inst_out_proof                        true
% 1.66/0.98  
% 1.66/0.98  ------ Resolution Options
% 1.66/0.98  
% 1.66/0.98  --resolution_flag                       true
% 1.66/0.98  --res_lit_sel                           adaptive
% 1.66/0.98  --res_lit_sel_side                      none
% 1.66/0.98  --res_ordering                          kbo
% 1.66/0.98  --res_to_prop_solver                    active
% 1.66/0.98  --res_prop_simpl_new                    false
% 1.66/0.98  --res_prop_simpl_given                  true
% 1.66/0.98  --res_passive_queue_type                priority_queues
% 1.66/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.66/0.98  --res_passive_queues_freq               [15;5]
% 1.66/0.98  --res_forward_subs                      full
% 1.66/0.98  --res_backward_subs                     full
% 1.66/0.98  --res_forward_subs_resolution           true
% 1.66/0.98  --res_backward_subs_resolution          true
% 1.66/0.98  --res_orphan_elimination                true
% 1.66/0.98  --res_time_limit                        2.
% 1.66/0.98  --res_out_proof                         true
% 1.66/0.98  
% 1.66/0.98  ------ Superposition Options
% 1.66/0.98  
% 1.66/0.98  --superposition_flag                    true
% 1.66/0.98  --sup_passive_queue_type                priority_queues
% 1.66/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.66/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.66/0.98  --demod_completeness_check              fast
% 1.66/0.98  --demod_use_ground                      true
% 1.66/0.98  --sup_to_prop_solver                    passive
% 1.66/0.98  --sup_prop_simpl_new                    true
% 1.66/0.98  --sup_prop_simpl_given                  true
% 1.66/0.98  --sup_fun_splitting                     false
% 1.66/0.98  --sup_smt_interval                      50000
% 1.66/0.98  
% 1.66/0.98  ------ Superposition Simplification Setup
% 1.66/0.98  
% 1.66/0.98  --sup_indices_passive                   []
% 1.66/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.66/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.66/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.66/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.66/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.66/0.98  --sup_full_bw                           [BwDemod]
% 1.66/0.98  --sup_immed_triv                        [TrivRules]
% 1.66/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.66/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.66/0.98  --sup_immed_bw_main                     []
% 1.66/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.66/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.66/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.66/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.66/0.98  
% 1.66/0.98  ------ Combination Options
% 1.66/0.98  
% 1.66/0.98  --comb_res_mult                         3
% 1.66/0.98  --comb_sup_mult                         2
% 1.66/0.98  --comb_inst_mult                        10
% 1.66/0.98  
% 1.66/0.98  ------ Debug Options
% 1.66/0.98  
% 1.66/0.98  --dbg_backtrace                         false
% 1.66/0.98  --dbg_dump_prop_clauses                 false
% 1.66/0.98  --dbg_dump_prop_clauses_file            -
% 1.66/0.98  --dbg_out_stat                          false
% 1.66/0.98  ------ Parsing...
% 1.66/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.66/0.98  
% 1.66/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 1.66/0.98  
% 1.66/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.66/0.98  
% 1.66/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.66/0.98  ------ Proving...
% 1.66/0.98  ------ Problem Properties 
% 1.66/0.98  
% 1.66/0.98  
% 1.66/0.98  clauses                                 16
% 1.66/0.98  conjectures                             2
% 1.66/0.98  EPR                                     1
% 1.66/0.98  Horn                                    15
% 1.66/0.98  unary                                   4
% 1.66/0.98  binary                                  6
% 1.66/0.98  lits                                    35
% 1.66/0.98  lits eq                                 19
% 1.66/0.98  fd_pure                                 0
% 1.66/0.98  fd_pseudo                               0
% 1.66/0.98  fd_cond                                 0
% 1.66/0.98  fd_pseudo_cond                          0
% 1.66/0.98  AC symbols                              0
% 1.66/0.98  
% 1.66/0.98  ------ Schedule dynamic 5 is on 
% 1.66/0.98  
% 1.66/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.66/0.98  
% 1.66/0.98  
% 1.66/0.98  ------ 
% 1.66/0.98  Current options:
% 1.66/0.98  ------ 
% 1.66/0.98  
% 1.66/0.98  ------ Input Options
% 1.66/0.98  
% 1.66/0.98  --out_options                           all
% 1.66/0.98  --tptp_safe_out                         true
% 1.66/0.98  --problem_path                          ""
% 1.66/0.98  --include_path                          ""
% 1.66/0.98  --clausifier                            res/vclausify_rel
% 1.66/0.98  --clausifier_options                    --mode clausify
% 1.66/0.98  --stdin                                 false
% 1.66/0.98  --stats_out                             all
% 1.66/0.98  
% 1.66/0.98  ------ General Options
% 1.66/0.98  
% 1.66/0.98  --fof                                   false
% 1.66/0.98  --time_out_real                         305.
% 1.66/0.98  --time_out_virtual                      -1.
% 1.66/0.98  --symbol_type_check                     false
% 1.66/0.98  --clausify_out                          false
% 1.66/0.98  --sig_cnt_out                           false
% 1.66/0.98  --trig_cnt_out                          false
% 1.66/0.98  --trig_cnt_out_tolerance                1.
% 1.66/0.98  --trig_cnt_out_sk_spl                   false
% 1.66/0.98  --abstr_cl_out                          false
% 1.66/0.98  
% 1.66/0.98  ------ Global Options
% 1.66/0.98  
% 1.66/0.98  --schedule                              default
% 1.66/0.98  --add_important_lit                     false
% 1.66/0.98  --prop_solver_per_cl                    1000
% 1.66/0.98  --min_unsat_core                        false
% 1.66/0.98  --soft_assumptions                      false
% 1.66/0.98  --soft_lemma_size                       3
% 1.66/0.98  --prop_impl_unit_size                   0
% 1.66/0.98  --prop_impl_unit                        []
% 1.66/0.98  --share_sel_clauses                     true
% 1.66/0.98  --reset_solvers                         false
% 1.66/0.98  --bc_imp_inh                            [conj_cone]
% 1.66/0.98  --conj_cone_tolerance                   3.
% 1.66/0.98  --extra_neg_conj                        none
% 1.66/0.98  --large_theory_mode                     true
% 1.66/0.98  --prolific_symb_bound                   200
% 1.66/0.98  --lt_threshold                          2000
% 1.66/0.98  --clause_weak_htbl                      true
% 1.66/0.98  --gc_record_bc_elim                     false
% 1.66/0.98  
% 1.66/0.98  ------ Preprocessing Options
% 1.66/0.98  
% 1.66/0.98  --preprocessing_flag                    true
% 1.66/0.98  --time_out_prep_mult                    0.1
% 1.66/0.98  --splitting_mode                        input
% 1.66/0.98  --splitting_grd                         true
% 1.66/0.98  --splitting_cvd                         false
% 1.66/0.98  --splitting_cvd_svl                     false
% 1.66/0.98  --splitting_nvd                         32
% 1.66/0.98  --sub_typing                            true
% 1.66/0.98  --prep_gs_sim                           true
% 1.66/0.98  --prep_unflatten                        true
% 1.66/0.98  --prep_res_sim                          true
% 1.66/0.98  --prep_upred                            true
% 1.66/0.98  --prep_sem_filter                       exhaustive
% 1.66/0.98  --prep_sem_filter_out                   false
% 1.66/0.98  --pred_elim                             true
% 1.66/0.98  --res_sim_input                         true
% 1.66/0.98  --eq_ax_congr_red                       true
% 1.66/0.98  --pure_diseq_elim                       true
% 1.66/0.98  --brand_transform                       false
% 1.66/0.98  --non_eq_to_eq                          false
% 1.66/0.98  --prep_def_merge                        true
% 1.66/0.98  --prep_def_merge_prop_impl              false
% 1.66/0.98  --prep_def_merge_mbd                    true
% 1.66/0.98  --prep_def_merge_tr_red                 false
% 1.66/0.98  --prep_def_merge_tr_cl                  false
% 1.66/0.98  --smt_preprocessing                     true
% 1.66/0.98  --smt_ac_axioms                         fast
% 1.66/0.98  --preprocessed_out                      false
% 1.66/0.98  --preprocessed_stats                    false
% 1.66/0.98  
% 1.66/0.98  ------ Abstraction refinement Options
% 1.66/0.98  
% 1.66/0.98  --abstr_ref                             []
% 1.66/0.98  --abstr_ref_prep                        false
% 1.66/0.98  --abstr_ref_until_sat                   false
% 1.66/0.98  --abstr_ref_sig_restrict                funpre
% 1.66/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.66/0.98  --abstr_ref_under                       []
% 1.66/0.98  
% 1.66/0.98  ------ SAT Options
% 1.66/0.98  
% 1.66/0.98  --sat_mode                              false
% 1.66/0.98  --sat_fm_restart_options                ""
% 1.66/0.98  --sat_gr_def                            false
% 1.66/0.98  --sat_epr_types                         true
% 1.66/0.98  --sat_non_cyclic_types                  false
% 1.66/0.98  --sat_finite_models                     false
% 1.66/0.98  --sat_fm_lemmas                         false
% 1.66/0.98  --sat_fm_prep                           false
% 1.66/0.98  --sat_fm_uc_incr                        true
% 1.66/0.98  --sat_out_model                         small
% 1.66/0.98  --sat_out_clauses                       false
% 1.66/0.98  
% 1.66/0.98  ------ QBF Options
% 1.66/0.98  
% 1.66/0.98  --qbf_mode                              false
% 1.66/0.98  --qbf_elim_univ                         false
% 1.66/0.98  --qbf_dom_inst                          none
% 1.66/0.98  --qbf_dom_pre_inst                      false
% 1.66/0.98  --qbf_sk_in                             false
% 1.66/0.98  --qbf_pred_elim                         true
% 1.66/0.98  --qbf_split                             512
% 1.66/0.98  
% 1.66/0.98  ------ BMC1 Options
% 1.66/0.98  
% 1.66/0.98  --bmc1_incremental                      false
% 1.66/0.98  --bmc1_axioms                           reachable_all
% 1.66/0.98  --bmc1_min_bound                        0
% 1.66/0.98  --bmc1_max_bound                        -1
% 1.66/0.98  --bmc1_max_bound_default                -1
% 1.66/0.98  --bmc1_symbol_reachability              true
% 1.66/0.98  --bmc1_property_lemmas                  false
% 1.66/0.98  --bmc1_k_induction                      false
% 1.66/0.98  --bmc1_non_equiv_states                 false
% 1.66/0.98  --bmc1_deadlock                         false
% 1.66/0.98  --bmc1_ucm                              false
% 1.66/0.98  --bmc1_add_unsat_core                   none
% 1.66/0.98  --bmc1_unsat_core_children              false
% 1.66/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.66/0.98  --bmc1_out_stat                         full
% 1.66/0.98  --bmc1_ground_init                      false
% 1.66/0.98  --bmc1_pre_inst_next_state              false
% 1.66/0.98  --bmc1_pre_inst_state                   false
% 1.66/0.98  --bmc1_pre_inst_reach_state             false
% 1.66/0.98  --bmc1_out_unsat_core                   false
% 1.66/0.98  --bmc1_aig_witness_out                  false
% 1.66/0.98  --bmc1_verbose                          false
% 1.66/0.98  --bmc1_dump_clauses_tptp                false
% 1.66/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.66/0.98  --bmc1_dump_file                        -
% 1.66/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.66/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.66/0.98  --bmc1_ucm_extend_mode                  1
% 1.66/0.98  --bmc1_ucm_init_mode                    2
% 1.66/0.98  --bmc1_ucm_cone_mode                    none
% 1.66/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.66/0.98  --bmc1_ucm_relax_model                  4
% 1.66/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.66/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.66/0.98  --bmc1_ucm_layered_model                none
% 1.66/0.98  --bmc1_ucm_max_lemma_size               10
% 1.66/0.98  
% 1.66/0.98  ------ AIG Options
% 1.66/0.98  
% 1.66/0.98  --aig_mode                              false
% 1.66/0.98  
% 1.66/0.98  ------ Instantiation Options
% 1.66/0.98  
% 1.66/0.98  --instantiation_flag                    true
% 1.66/0.98  --inst_sos_flag                         false
% 1.66/0.98  --inst_sos_phase                        true
% 1.66/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.66/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.66/0.98  --inst_lit_sel_side                     none
% 1.66/0.98  --inst_solver_per_active                1400
% 1.66/0.98  --inst_solver_calls_frac                1.
% 1.66/0.98  --inst_passive_queue_type               priority_queues
% 1.66/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.66/0.98  --inst_passive_queues_freq              [25;2]
% 1.66/0.98  --inst_dismatching                      true
% 1.66/0.98  --inst_eager_unprocessed_to_passive     true
% 1.66/0.98  --inst_prop_sim_given                   true
% 1.66/0.98  --inst_prop_sim_new                     false
% 1.66/0.98  --inst_subs_new                         false
% 1.66/0.98  --inst_eq_res_simp                      false
% 1.66/0.98  --inst_subs_given                       false
% 1.66/0.98  --inst_orphan_elimination               true
% 1.66/0.98  --inst_learning_loop_flag               true
% 1.66/0.98  --inst_learning_start                   3000
% 1.66/0.98  --inst_learning_factor                  2
% 1.66/0.98  --inst_start_prop_sim_after_learn       3
% 1.66/0.98  --inst_sel_renew                        solver
% 1.66/0.98  --inst_lit_activity_flag                true
% 1.66/0.98  --inst_restr_to_given                   false
% 1.66/0.98  --inst_activity_threshold               500
% 1.66/0.98  --inst_out_proof                        true
% 1.66/0.98  
% 1.66/0.98  ------ Resolution Options
% 1.66/0.98  
% 1.66/0.98  --resolution_flag                       false
% 1.66/0.98  --res_lit_sel                           adaptive
% 1.66/0.98  --res_lit_sel_side                      none
% 1.66/0.98  --res_ordering                          kbo
% 1.66/0.98  --res_to_prop_solver                    active
% 1.66/0.98  --res_prop_simpl_new                    false
% 1.66/0.98  --res_prop_simpl_given                  true
% 1.66/0.98  --res_passive_queue_type                priority_queues
% 1.66/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.66/0.98  --res_passive_queues_freq               [15;5]
% 1.66/0.98  --res_forward_subs                      full
% 1.66/0.98  --res_backward_subs                     full
% 1.66/0.98  --res_forward_subs_resolution           true
% 1.66/0.98  --res_backward_subs_resolution          true
% 1.66/0.98  --res_orphan_elimination                true
% 1.66/0.98  --res_time_limit                        2.
% 1.66/0.98  --res_out_proof                         true
% 1.66/0.98  
% 1.66/0.98  ------ Superposition Options
% 1.66/0.98  
% 1.66/0.98  --superposition_flag                    true
% 1.66/0.98  --sup_passive_queue_type                priority_queues
% 1.66/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.66/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.66/0.98  --demod_completeness_check              fast
% 1.66/0.98  --demod_use_ground                      true
% 1.66/0.98  --sup_to_prop_solver                    passive
% 1.66/0.98  --sup_prop_simpl_new                    true
% 1.66/0.98  --sup_prop_simpl_given                  true
% 1.66/0.98  --sup_fun_splitting                     false
% 1.66/0.98  --sup_smt_interval                      50000
% 1.66/0.98  
% 1.66/0.98  ------ Superposition Simplification Setup
% 1.66/0.98  
% 1.66/0.98  --sup_indices_passive                   []
% 1.66/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.66/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.66/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.66/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.66/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.66/0.98  --sup_full_bw                           [BwDemod]
% 1.66/0.98  --sup_immed_triv                        [TrivRules]
% 1.66/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.66/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.66/0.98  --sup_immed_bw_main                     []
% 1.66/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.66/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.66/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.66/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.66/0.98  
% 1.66/0.98  ------ Combination Options
% 1.66/0.98  
% 1.66/0.98  --comb_res_mult                         3
% 1.66/0.98  --comb_sup_mult                         2
% 1.66/0.98  --comb_inst_mult                        10
% 1.66/0.98  
% 1.66/0.98  ------ Debug Options
% 1.66/0.98  
% 1.66/0.98  --dbg_backtrace                         false
% 1.66/0.98  --dbg_dump_prop_clauses                 false
% 1.66/0.98  --dbg_dump_prop_clauses_file            -
% 1.66/0.98  --dbg_out_stat                          false
% 1.66/0.98  
% 1.66/0.98  
% 1.66/0.98  
% 1.66/0.98  
% 1.66/0.98  ------ Proving...
% 1.66/0.98  
% 1.66/0.98  
% 1.66/0.98  % SZS status Theorem for theBenchmark.p
% 1.66/0.98  
% 1.66/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 1.66/0.98  
% 1.66/0.98  fof(f11,axiom,(
% 1.66/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.66/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.66/0.98  
% 1.66/0.98  fof(f17,plain,(
% 1.66/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.66/0.98    inference(pure_predicate_removal,[],[f11])).
% 1.66/0.98  
% 1.66/0.98  fof(f24,plain,(
% 1.66/0.98    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.66/0.98    inference(ennf_transformation,[],[f17])).
% 1.66/0.98  
% 1.66/0.98  fof(f50,plain,(
% 1.66/0.98    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.66/0.98    inference(cnf_transformation,[],[f24])).
% 1.66/0.98  
% 1.66/0.98  fof(f7,axiom,(
% 1.66/0.98    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.66/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.66/0.98  
% 1.66/0.98  fof(f20,plain,(
% 1.66/0.98    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.66/0.98    inference(ennf_transformation,[],[f7])).
% 1.66/0.98  
% 1.66/0.98  fof(f33,plain,(
% 1.66/0.98    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.66/0.98    inference(nnf_transformation,[],[f20])).
% 1.66/0.98  
% 1.66/0.98  fof(f45,plain,(
% 1.66/0.98    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.66/0.98    inference(cnf_transformation,[],[f33])).
% 1.66/0.98  
% 1.66/0.98  fof(f15,conjecture,(
% 1.66/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 1.66/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.66/0.98  
% 1.66/0.98  fof(f16,negated_conjecture,(
% 1.66/0.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 1.66/0.98    inference(negated_conjecture,[],[f15])).
% 1.66/0.98  
% 1.66/0.98  fof(f29,plain,(
% 1.66/0.98    ? [X0,X1,X2] : ((k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 1.66/0.98    inference(ennf_transformation,[],[f16])).
% 1.66/0.98  
% 1.66/0.98  fof(f30,plain,(
% 1.66/0.98    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 1.66/0.98    inference(flattening,[],[f29])).
% 1.66/0.98  
% 1.66/0.98  fof(f35,plain,(
% 1.66/0.98    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_tarski(k1_funct_1(sK2,sK0)) != k2_relset_1(k1_tarski(sK0),sK1,sK2) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2))),
% 1.66/0.98    introduced(choice_axiom,[])).
% 1.66/0.98  
% 1.66/0.98  fof(f36,plain,(
% 1.66/0.98    k1_tarski(k1_funct_1(sK2,sK0)) != k2_relset_1(k1_tarski(sK0),sK1,sK2) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2)),
% 1.66/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f35])).
% 1.66/0.98  
% 1.66/0.98  fof(f61,plain,(
% 1.66/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.66/0.98    inference(cnf_transformation,[],[f36])).
% 1.66/0.98  
% 1.66/0.98  fof(f1,axiom,(
% 1.66/0.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.66/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.66/0.98  
% 1.66/0.98  fof(f37,plain,(
% 1.66/0.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.66/0.98    inference(cnf_transformation,[],[f1])).
% 1.66/0.98  
% 1.66/0.98  fof(f2,axiom,(
% 1.66/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.66/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.66/0.98  
% 1.66/0.98  fof(f38,plain,(
% 1.66/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.66/0.98    inference(cnf_transformation,[],[f2])).
% 1.66/0.98  
% 1.66/0.98  fof(f3,axiom,(
% 1.66/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.66/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.66/0.98  
% 1.66/0.98  fof(f39,plain,(
% 1.66/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.66/0.98    inference(cnf_transformation,[],[f3])).
% 1.66/0.98  
% 1.66/0.98  fof(f64,plain,(
% 1.66/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.66/0.98    inference(definition_unfolding,[],[f38,f39])).
% 1.66/0.98  
% 1.66/0.98  fof(f65,plain,(
% 1.66/0.98    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.66/0.98    inference(definition_unfolding,[],[f37,f64])).
% 1.66/0.98  
% 1.66/0.98  fof(f72,plain,(
% 1.66/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 1.66/0.98    inference(definition_unfolding,[],[f61,f65])).
% 1.66/0.98  
% 1.66/0.98  fof(f5,axiom,(
% 1.66/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.66/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.66/0.98  
% 1.66/0.98  fof(f18,plain,(
% 1.66/0.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.66/0.98    inference(ennf_transformation,[],[f5])).
% 1.66/0.98  
% 1.66/0.98  fof(f43,plain,(
% 1.66/0.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.66/0.98    inference(cnf_transformation,[],[f18])).
% 1.66/0.98  
% 1.66/0.98  fof(f8,axiom,(
% 1.66/0.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.66/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.66/0.98  
% 1.66/0.98  fof(f47,plain,(
% 1.66/0.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.66/0.98    inference(cnf_transformation,[],[f8])).
% 1.66/0.98  
% 1.66/0.98  fof(f60,plain,(
% 1.66/0.98    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 1.66/0.98    inference(cnf_transformation,[],[f36])).
% 1.66/0.98  
% 1.66/0.98  fof(f73,plain,(
% 1.66/0.98    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 1.66/0.98    inference(definition_unfolding,[],[f60,f65])).
% 1.66/0.98  
% 1.66/0.98  fof(f14,axiom,(
% 1.66/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.66/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.66/0.98  
% 1.66/0.98  fof(f27,plain,(
% 1.66/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.66/0.98    inference(ennf_transformation,[],[f14])).
% 1.66/0.98  
% 1.66/0.98  fof(f28,plain,(
% 1.66/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.66/0.98    inference(flattening,[],[f27])).
% 1.66/0.98  
% 1.66/0.98  fof(f34,plain,(
% 1.66/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.66/0.98    inference(nnf_transformation,[],[f28])).
% 1.66/0.98  
% 1.66/0.98  fof(f53,plain,(
% 1.66/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.66/0.98    inference(cnf_transformation,[],[f34])).
% 1.66/0.98  
% 1.66/0.98  fof(f62,plain,(
% 1.66/0.98    k1_xboole_0 != sK1),
% 1.66/0.98    inference(cnf_transformation,[],[f36])).
% 1.66/0.98  
% 1.66/0.98  fof(f12,axiom,(
% 1.66/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.66/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.66/0.98  
% 1.66/0.98  fof(f25,plain,(
% 1.66/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.66/0.98    inference(ennf_transformation,[],[f12])).
% 1.66/0.98  
% 1.66/0.98  fof(f51,plain,(
% 1.66/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.66/0.98    inference(cnf_transformation,[],[f25])).
% 1.66/0.98  
% 1.66/0.98  fof(f4,axiom,(
% 1.66/0.98    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.66/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.66/0.98  
% 1.66/0.98  fof(f31,plain,(
% 1.66/0.98    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.66/0.98    inference(nnf_transformation,[],[f4])).
% 1.66/0.98  
% 1.66/0.98  fof(f32,plain,(
% 1.66/0.98    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.66/0.98    inference(flattening,[],[f31])).
% 1.66/0.98  
% 1.66/0.98  fof(f41,plain,(
% 1.66/0.98    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 1.66/0.98    inference(cnf_transformation,[],[f32])).
% 1.66/0.98  
% 1.66/0.98  fof(f67,plain,(
% 1.66/0.98    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)) )),
% 1.66/0.98    inference(definition_unfolding,[],[f41,f64])).
% 1.66/0.98  
% 1.66/0.98  fof(f10,axiom,(
% 1.66/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)))),
% 1.66/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.66/0.98  
% 1.66/0.98  fof(f22,plain,(
% 1.66/0.98    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.66/0.98    inference(ennf_transformation,[],[f10])).
% 1.66/0.98  
% 1.66/0.98  fof(f23,plain,(
% 1.66/0.98    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.66/0.98    inference(flattening,[],[f22])).
% 1.66/0.98  
% 1.66/0.98  fof(f49,plain,(
% 1.66/0.98    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.66/0.98    inference(cnf_transformation,[],[f23])).
% 1.66/0.98  
% 1.66/0.98  fof(f70,plain,(
% 1.66/0.98    ( ! [X0,X1] : (k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.66/0.98    inference(definition_unfolding,[],[f49,f65])).
% 1.66/0.98  
% 1.66/0.98  fof(f59,plain,(
% 1.66/0.98    v1_funct_1(sK2)),
% 1.66/0.98    inference(cnf_transformation,[],[f36])).
% 1.66/0.98  
% 1.66/0.98  fof(f6,axiom,(
% 1.66/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 1.66/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.66/0.98  
% 1.66/0.98  fof(f19,plain,(
% 1.66/0.98    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 1.66/0.98    inference(ennf_transformation,[],[f6])).
% 1.66/0.98  
% 1.66/0.98  fof(f44,plain,(
% 1.66/0.98    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 1.66/0.98    inference(cnf_transformation,[],[f19])).
% 1.66/0.98  
% 1.66/0.98  fof(f69,plain,(
% 1.66/0.98    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 1.66/0.98    inference(definition_unfolding,[],[f44,f65])).
% 1.66/0.98  
% 1.66/0.98  fof(f9,axiom,(
% 1.66/0.98    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 1.66/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.66/0.98  
% 1.66/0.98  fof(f21,plain,(
% 1.66/0.98    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 1.66/0.98    inference(ennf_transformation,[],[f9])).
% 1.66/0.98  
% 1.66/0.98  fof(f48,plain,(
% 1.66/0.98    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.66/0.98    inference(cnf_transformation,[],[f21])).
% 1.66/0.98  
% 1.66/0.98  fof(f13,axiom,(
% 1.66/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 1.66/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.66/0.98  
% 1.66/0.98  fof(f26,plain,(
% 1.66/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.66/0.98    inference(ennf_transformation,[],[f13])).
% 1.66/0.98  
% 1.66/0.98  fof(f52,plain,(
% 1.66/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.66/0.98    inference(cnf_transformation,[],[f26])).
% 1.66/0.98  
% 1.66/0.98  fof(f63,plain,(
% 1.66/0.98    k1_tarski(k1_funct_1(sK2,sK0)) != k2_relset_1(k1_tarski(sK0),sK1,sK2)),
% 1.66/0.98    inference(cnf_transformation,[],[f36])).
% 1.66/0.98  
% 1.66/0.98  fof(f71,plain,(
% 1.66/0.98    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)),
% 1.66/0.98    inference(definition_unfolding,[],[f63,f65,f65])).
% 1.66/0.98  
% 1.66/0.98  cnf(c_10,plain,
% 1.66/0.98      ( v4_relat_1(X0,X1)
% 1.66/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 1.66/0.98      inference(cnf_transformation,[],[f50]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_6,plain,
% 1.66/0.98      ( ~ v4_relat_1(X0,X1)
% 1.66/0.98      | r1_tarski(k1_relat_1(X0),X1)
% 1.66/0.98      | ~ v1_relat_1(X0) ),
% 1.66/0.98      inference(cnf_transformation,[],[f45]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_276,plain,
% 1.66/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.66/0.98      | r1_tarski(k1_relat_1(X0),X1)
% 1.66/0.98      | ~ v1_relat_1(X0) ),
% 1.66/0.98      inference(resolution,[status(thm)],[c_10,c_6]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_21,negated_conjecture,
% 1.66/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
% 1.66/0.98      inference(cnf_transformation,[],[f72]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_373,plain,
% 1.66/0.98      ( r1_tarski(k1_relat_1(X0),X1)
% 1.66/0.98      | ~ v1_relat_1(X0)
% 1.66/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 1.66/0.98      | sK2 != X0 ),
% 1.66/0.98      inference(resolution_lifted,[status(thm)],[c_276,c_21]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_374,plain,
% 1.66/0.98      ( r1_tarski(k1_relat_1(sK2),X0)
% 1.66/0.98      | ~ v1_relat_1(sK2)
% 1.66/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 1.66/0.98      inference(unflattening,[status(thm)],[c_373]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_811,plain,
% 1.66/0.98      ( r1_tarski(k1_relat_1(sK2),X0_49)
% 1.66/0.98      | ~ v1_relat_1(sK2)
% 1.66/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)) ),
% 1.66/0.98      inference(subtyping,[status(esa)],[c_374]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_1055,plain,
% 1.66/0.98      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))
% 1.66/0.98      | r1_tarski(k1_relat_1(sK2),X0_49) = iProver_top
% 1.66/0.98      | v1_relat_1(sK2) != iProver_top ),
% 1.66/0.98      inference(predicate_to_equality,[status(thm)],[c_811]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_878,plain,
% 1.66/0.98      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))
% 1.66/0.98      | r1_tarski(k1_relat_1(sK2),X0_49) = iProver_top
% 1.66/0.98      | v1_relat_1(sK2) != iProver_top ),
% 1.66/0.98      inference(predicate_to_equality,[status(thm)],[c_811]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_825,plain,( X0_51 = X0_51 ),theory(equality) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_1154,plain,
% 1.66/0.98      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) = k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
% 1.66/0.98      inference(instantiation,[status(thm)],[c_825]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_3,plain,
% 1.66/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.66/0.98      | ~ v1_relat_1(X1)
% 1.66/0.98      | v1_relat_1(X0) ),
% 1.66/0.98      inference(cnf_transformation,[],[f43]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_358,plain,
% 1.66/0.98      ( ~ v1_relat_1(X0)
% 1.66/0.98      | v1_relat_1(X1)
% 1.66/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(X0)
% 1.66/0.98      | sK2 != X1 ),
% 1.66/0.98      inference(resolution_lifted,[status(thm)],[c_3,c_21]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_359,plain,
% 1.66/0.98      ( ~ v1_relat_1(X0)
% 1.66/0.98      | v1_relat_1(sK2)
% 1.66/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(X0) ),
% 1.66/0.98      inference(unflattening,[status(thm)],[c_358]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_812,plain,
% 1.66/0.98      ( ~ v1_relat_1(X0_49)
% 1.66/0.98      | v1_relat_1(sK2)
% 1.66/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(X0_49) ),
% 1.66/0.98      inference(subtyping,[status(esa)],[c_359]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_1149,plain,
% 1.66/0.98      ( ~ v1_relat_1(k2_zfmisc_1(X0_49,X1_49))
% 1.66/0.98      | v1_relat_1(sK2)
% 1.66/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)) ),
% 1.66/0.98      inference(instantiation,[status(thm)],[c_812]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_1218,plain,
% 1.66/0.98      ( ~ v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
% 1.66/0.98      | v1_relat_1(sK2)
% 1.66/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
% 1.66/0.98      inference(instantiation,[status(thm)],[c_1149]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_1219,plain,
% 1.66/0.98      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
% 1.66/0.98      | v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != iProver_top
% 1.66/0.98      | v1_relat_1(sK2) = iProver_top ),
% 1.66/0.98      inference(predicate_to_equality,[status(thm)],[c_1218]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_7,plain,
% 1.66/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 1.66/0.98      inference(cnf_transformation,[],[f47]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_817,plain,
% 1.66/0.98      ( v1_relat_1(k2_zfmisc_1(X0_49,X1_49)) ),
% 1.66/0.98      inference(subtyping,[status(esa)],[c_7]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_1297,plain,
% 1.66/0.98      ( v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
% 1.66/0.98      inference(instantiation,[status(thm)],[c_817]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_1298,plain,
% 1.66/0.98      ( v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) = iProver_top ),
% 1.66/0.98      inference(predicate_to_equality,[status(thm)],[c_1297]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_1537,plain,
% 1.66/0.98      ( r1_tarski(k1_relat_1(sK2),X0_49) = iProver_top
% 1.66/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)) ),
% 1.66/0.98      inference(global_propositional_subsumption,
% 1.66/0.98                [status(thm)],
% 1.66/0.98                [c_1055,c_878,c_1154,c_1219,c_1298]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_1538,plain,
% 1.66/0.98      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))
% 1.66/0.98      | r1_tarski(k1_relat_1(sK2),X0_49) = iProver_top ),
% 1.66/0.98      inference(renaming,[status(thm)],[c_1537]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_22,negated_conjecture,
% 1.66/0.98      ( v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
% 1.66/0.98      inference(cnf_transformation,[],[f73]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_18,plain,
% 1.66/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 1.66/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.66/0.98      | k1_relset_1(X1,X2,X0) = X1
% 1.66/0.98      | k1_xboole_0 = X2 ),
% 1.66/0.98      inference(cnf_transformation,[],[f53]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_388,plain,
% 1.66/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 1.66/0.98      | k1_relset_1(X1,X2,X0) = X1
% 1.66/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 1.66/0.98      | sK2 != X0
% 1.66/0.98      | k1_xboole_0 = X2 ),
% 1.66/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_21]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_389,plain,
% 1.66/0.98      ( ~ v1_funct_2(sK2,X0,X1)
% 1.66/0.98      | k1_relset_1(X0,X1,sK2) = X0
% 1.66/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.66/0.98      | k1_xboole_0 = X1 ),
% 1.66/0.98      inference(unflattening,[status(thm)],[c_388]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_618,plain,
% 1.66/0.98      ( k2_enumset1(sK0,sK0,sK0,sK0) != X0
% 1.66/0.98      | k1_relset_1(X0,X1,sK2) = X0
% 1.66/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.66/0.98      | sK1 != X1
% 1.66/0.98      | sK2 != sK2
% 1.66/0.98      | k1_xboole_0 = X1 ),
% 1.66/0.98      inference(resolution_lifted,[status(thm)],[c_22,c_389]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_619,plain,
% 1.66/0.98      ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0)
% 1.66/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
% 1.66/0.98      | k1_xboole_0 = sK1 ),
% 1.66/0.98      inference(unflattening,[status(thm)],[c_618]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_20,negated_conjecture,
% 1.66/0.98      ( k1_xboole_0 != sK1 ),
% 1.66/0.98      inference(cnf_transformation,[],[f62]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_620,plain,
% 1.66/0.98      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
% 1.66/0.98      | k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0) ),
% 1.66/0.98      inference(global_propositional_subsumption,
% 1.66/0.98                [status(thm)],
% 1.66/0.98                [c_619,c_20]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_621,plain,
% 1.66/0.98      ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0)
% 1.66/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
% 1.66/0.98      inference(renaming,[status(thm)],[c_620]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_679,plain,
% 1.66/0.98      ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0) ),
% 1.66/0.98      inference(equality_resolution_simp,[status(thm)],[c_621]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_806,plain,
% 1.66/0.98      ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0) ),
% 1.66/0.98      inference(subtyping,[status(esa)],[c_679]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_11,plain,
% 1.66/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.66/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 1.66/0.98      inference(cnf_transformation,[],[f51]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_433,plain,
% 1.66/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 1.66/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.66/0.98      | sK2 != X2 ),
% 1.66/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_21]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_434,plain,
% 1.66/0.98      ( k1_relset_1(X0,X1,sK2) = k1_relat_1(sK2)
% 1.66/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 1.66/0.98      inference(unflattening,[status(thm)],[c_433]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_809,plain,
% 1.66/0.98      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))
% 1.66/0.98      | k1_relset_1(X0_49,X1_49,sK2) = k1_relat_1(sK2) ),
% 1.66/0.98      inference(subtyping,[status(esa)],[c_434]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_1177,plain,
% 1.66/0.98      ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k1_relat_1(sK2) ),
% 1.66/0.98      inference(equality_resolution,[status(thm)],[c_809]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_1241,plain,
% 1.66/0.98      ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) ),
% 1.66/0.98      inference(light_normalisation,[status(thm)],[c_806,c_1177]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_1543,plain,
% 1.66/0.98      ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))
% 1.66/0.98      | r1_tarski(k1_relat_1(sK2),X0_49) = iProver_top ),
% 1.66/0.98      inference(light_normalisation,[status(thm)],[c_1538,c_1241]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_1549,plain,
% 1.66/0.98      ( r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) = iProver_top ),
% 1.66/0.98      inference(equality_resolution,[status(thm)],[c_1543]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_1,plain,
% 1.66/0.98      ( r2_hidden(X0,X1) | ~ r1_tarski(k2_enumset1(X2,X2,X2,X0),X1) ),
% 1.66/0.98      inference(cnf_transformation,[],[f67]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_820,plain,
% 1.66/0.98      ( r2_hidden(X0_50,X0_49)
% 1.66/0.98      | ~ r1_tarski(k2_enumset1(X1_50,X1_50,X1_50,X0_50),X0_49) ),
% 1.66/0.98      inference(subtyping,[status(esa)],[c_1]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_1048,plain,
% 1.66/0.98      ( r2_hidden(X0_50,X0_49) = iProver_top
% 1.66/0.98      | r1_tarski(k2_enumset1(X1_50,X1_50,X1_50,X0_50),X0_49) != iProver_top ),
% 1.66/0.98      inference(predicate_to_equality,[status(thm)],[c_820]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_1314,plain,
% 1.66/0.98      ( r2_hidden(sK0,X0_49) = iProver_top
% 1.66/0.98      | r1_tarski(k1_relat_1(sK2),X0_49) != iProver_top ),
% 1.66/0.98      inference(superposition,[status(thm)],[c_1241,c_1048]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_1891,plain,
% 1.66/0.98      ( r2_hidden(sK0,k1_relat_1(sK2)) = iProver_top ),
% 1.66/0.98      inference(superposition,[status(thm)],[c_1549,c_1314]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_9,plain,
% 1.66/0.98      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 1.66/0.98      | ~ v1_funct_1(X1)
% 1.66/0.98      | ~ v1_relat_1(X1)
% 1.66/0.98      | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ),
% 1.66/0.98      inference(cnf_transformation,[],[f70]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_23,negated_conjecture,
% 1.66/0.98      ( v1_funct_1(sK2) ),
% 1.66/0.98      inference(cnf_transformation,[],[f59]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_257,plain,
% 1.66/0.98      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 1.66/0.98      | ~ v1_relat_1(X1)
% 1.66/0.98      | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
% 1.66/0.98      | sK2 != X1 ),
% 1.66/0.98      inference(resolution_lifted,[status(thm)],[c_9,c_23]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_258,plain,
% 1.66/0.98      ( ~ r2_hidden(X0,k1_relat_1(sK2))
% 1.66/0.98      | ~ v1_relat_1(sK2)
% 1.66/0.98      | k2_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)) = k11_relat_1(sK2,X0) ),
% 1.66/0.98      inference(unflattening,[status(thm)],[c_257]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_813,plain,
% 1.66/0.98      ( ~ r2_hidden(X0_50,k1_relat_1(sK2))
% 1.66/0.98      | ~ v1_relat_1(sK2)
% 1.66/0.98      | k2_enumset1(k1_funct_1(sK2,X0_50),k1_funct_1(sK2,X0_50),k1_funct_1(sK2,X0_50),k1_funct_1(sK2,X0_50)) = k11_relat_1(sK2,X0_50) ),
% 1.66/0.98      inference(subtyping,[status(esa)],[c_258]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_1053,plain,
% 1.66/0.98      ( k2_enumset1(k1_funct_1(sK2,X0_50),k1_funct_1(sK2,X0_50),k1_funct_1(sK2,X0_50),k1_funct_1(sK2,X0_50)) = k11_relat_1(sK2,X0_50)
% 1.66/0.98      | r2_hidden(X0_50,k1_relat_1(sK2)) != iProver_top
% 1.66/0.98      | v1_relat_1(sK2) != iProver_top ),
% 1.66/0.98      inference(predicate_to_equality,[status(thm)],[c_813]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_872,plain,
% 1.66/0.98      ( k2_enumset1(k1_funct_1(sK2,X0_50),k1_funct_1(sK2,X0_50),k1_funct_1(sK2,X0_50),k1_funct_1(sK2,X0_50)) = k11_relat_1(sK2,X0_50)
% 1.66/0.98      | r2_hidden(X0_50,k1_relat_1(sK2)) != iProver_top
% 1.66/0.98      | v1_relat_1(sK2) != iProver_top ),
% 1.66/0.98      inference(predicate_to_equality,[status(thm)],[c_813]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_1552,plain,
% 1.66/0.98      ( r2_hidden(X0_50,k1_relat_1(sK2)) != iProver_top
% 1.66/0.98      | k2_enumset1(k1_funct_1(sK2,X0_50),k1_funct_1(sK2,X0_50),k1_funct_1(sK2,X0_50),k1_funct_1(sK2,X0_50)) = k11_relat_1(sK2,X0_50) ),
% 1.66/0.98      inference(global_propositional_subsumption,
% 1.66/0.98                [status(thm)],
% 1.66/0.98                [c_1053,c_872,c_1154,c_1219,c_1298]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_1553,plain,
% 1.66/0.98      ( k2_enumset1(k1_funct_1(sK2,X0_50),k1_funct_1(sK2,X0_50),k1_funct_1(sK2,X0_50),k1_funct_1(sK2,X0_50)) = k11_relat_1(sK2,X0_50)
% 1.66/0.98      | r2_hidden(X0_50,k1_relat_1(sK2)) != iProver_top ),
% 1.66/0.98      inference(renaming,[status(thm)],[c_1552]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_1960,plain,
% 1.66/0.98      ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k11_relat_1(sK2,sK0) ),
% 1.66/0.98      inference(superposition,[status(thm)],[c_1891,c_1553]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_1054,plain,
% 1.66/0.98      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(X0_49)
% 1.66/0.98      | v1_relat_1(X0_49) != iProver_top
% 1.66/0.98      | v1_relat_1(sK2) = iProver_top ),
% 1.66/0.98      inference(predicate_to_equality,[status(thm)],[c_812]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_1477,plain,
% 1.66/0.98      ( v1_relat_1(sK2) = iProver_top ),
% 1.66/0.98      inference(global_propositional_subsumption,
% 1.66/0.98                [status(thm)],
% 1.66/0.98                [c_1054,c_1154,c_1219,c_1298]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_4,plain,
% 1.66/0.98      ( ~ v1_relat_1(X0)
% 1.66/0.98      | k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
% 1.66/0.98      inference(cnf_transformation,[],[f69]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_818,plain,
% 1.66/0.98      ( ~ v1_relat_1(X0_49)
% 1.66/0.98      | k9_relat_1(X0_49,k2_enumset1(X0_50,X0_50,X0_50,X0_50)) = k11_relat_1(X0_49,X0_50) ),
% 1.66/0.98      inference(subtyping,[status(esa)],[c_4]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_1050,plain,
% 1.66/0.98      ( k9_relat_1(X0_49,k2_enumset1(X0_50,X0_50,X0_50,X0_50)) = k11_relat_1(X0_49,X0_50)
% 1.66/0.98      | v1_relat_1(X0_49) != iProver_top ),
% 1.66/0.98      inference(predicate_to_equality,[status(thm)],[c_818]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_1672,plain,
% 1.66/0.98      ( k9_relat_1(sK2,k2_enumset1(X0_50,X0_50,X0_50,X0_50)) = k11_relat_1(sK2,X0_50) ),
% 1.66/0.98      inference(superposition,[status(thm)],[c_1477,c_1050]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_1681,plain,
% 1.66/0.98      ( k9_relat_1(sK2,k1_relat_1(sK2)) = k11_relat_1(sK2,sK0) ),
% 1.66/0.98      inference(superposition,[status(thm)],[c_1241,c_1672]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_8,plain,
% 1.66/0.98      ( ~ v1_relat_1(X0)
% 1.66/0.98      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 1.66/0.98      inference(cnf_transformation,[],[f48]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_816,plain,
% 1.66/0.98      ( ~ v1_relat_1(X0_49)
% 1.66/0.98      | k9_relat_1(X0_49,k1_relat_1(X0_49)) = k2_relat_1(X0_49) ),
% 1.66/0.98      inference(subtyping,[status(esa)],[c_8]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_1052,plain,
% 1.66/0.98      ( k9_relat_1(X0_49,k1_relat_1(X0_49)) = k2_relat_1(X0_49)
% 1.66/0.98      | v1_relat_1(X0_49) != iProver_top ),
% 1.66/0.98      inference(predicate_to_equality,[status(thm)],[c_816]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_1482,plain,
% 1.66/0.98      ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
% 1.66/0.98      inference(superposition,[status(thm)],[c_1477,c_1052]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_1682,plain,
% 1.66/0.98      ( k11_relat_1(sK2,sK0) = k2_relat_1(sK2) ),
% 1.66/0.98      inference(light_normalisation,[status(thm)],[c_1681,c_1482]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_1961,plain,
% 1.66/0.98      ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2) ),
% 1.66/0.98      inference(light_normalisation,[status(thm)],[c_1960,c_1682]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_826,plain,
% 1.66/0.98      ( X0_49 != X1_49 | X2_49 != X1_49 | X2_49 = X0_49 ),
% 1.66/0.98      theory(equality) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_1173,plain,
% 1.66/0.98      ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != X0_49
% 1.66/0.98      | k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)
% 1.66/0.98      | k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != X0_49 ),
% 1.66/0.98      inference(instantiation,[status(thm)],[c_826]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_1203,plain,
% 1.66/0.98      ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)
% 1.66/0.98      | k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relat_1(sK2)
% 1.66/0.98      | k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_relat_1(sK2) ),
% 1.66/0.98      inference(instantiation,[status(thm)],[c_1173]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_12,plain,
% 1.66/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.66/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 1.66/0.98      inference(cnf_transformation,[],[f52]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_424,plain,
% 1.66/0.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 1.66/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.66/0.98      | sK2 != X2 ),
% 1.66/0.98      inference(resolution_lifted,[status(thm)],[c_12,c_21]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_425,plain,
% 1.66/0.98      ( k2_relset_1(X0,X1,sK2) = k2_relat_1(sK2)
% 1.66/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 1.66/0.98      inference(unflattening,[status(thm)],[c_424]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_810,plain,
% 1.66/0.98      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))
% 1.66/0.98      | k2_relset_1(X0_49,X1_49,sK2) = k2_relat_1(sK2) ),
% 1.66/0.98      inference(subtyping,[status(esa)],[c_425]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_1155,plain,
% 1.66/0.98      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
% 1.66/0.98      | k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2) ),
% 1.66/0.98      inference(instantiation,[status(thm)],[c_810]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_19,negated_conjecture,
% 1.66/0.98      ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) ),
% 1.66/0.98      inference(cnf_transformation,[],[f71]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(c_815,negated_conjecture,
% 1.66/0.98      ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) ),
% 1.66/0.98      inference(subtyping,[status(esa)],[c_19]) ).
% 1.66/0.98  
% 1.66/0.98  cnf(contradiction,plain,
% 1.66/0.98      ( $false ),
% 1.66/0.98      inference(minisat,[status(thm)],[c_1961,c_1203,c_1155,c_1154,c_815]) ).
% 1.66/0.98  
% 1.66/0.98  
% 1.66/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 1.66/0.98  
% 1.66/0.98  ------                               Statistics
% 1.66/0.98  
% 1.66/0.98  ------ General
% 1.66/0.98  
% 1.66/0.98  abstr_ref_over_cycles:                  0
% 1.66/0.98  abstr_ref_under_cycles:                 0
% 1.66/0.98  gc_basic_clause_elim:                   0
% 1.66/0.98  forced_gc_time:                         0
% 1.66/0.98  parsing_time:                           0.008
% 1.66/0.98  unif_index_cands_time:                  0.
% 1.66/0.98  unif_index_add_time:                    0.
% 1.66/0.98  orderings_time:                         0.
% 1.66/0.98  out_proof_time:                         0.013
% 1.66/0.98  total_time:                             0.099
% 1.66/0.98  num_of_symbols:                         55
% 1.66/0.99  num_of_terms:                           1768
% 1.66/0.99  
% 1.66/0.99  ------ Preprocessing
% 1.66/0.99  
% 1.66/0.99  num_of_splits:                          0
% 1.66/0.99  num_of_split_atoms:                     0
% 1.66/0.99  num_of_reused_defs:                     0
% 1.66/0.99  num_eq_ax_congr_red:                    19
% 1.66/0.99  num_of_sem_filtered_clauses:            1
% 1.66/0.99  num_of_subtypes:                        3
% 1.66/0.99  monotx_restored_types:                  0
% 1.66/0.99  sat_num_of_epr_types:                   0
% 1.66/0.99  sat_num_of_non_cyclic_types:            0
% 1.66/0.99  sat_guarded_non_collapsed_types:        0
% 1.66/0.99  num_pure_diseq_elim:                    0
% 1.66/0.99  simp_replaced_by:                       0
% 1.66/0.99  res_preprocessed:                       109
% 1.66/0.99  prep_upred:                             0
% 1.66/0.99  prep_unflattend:                        36
% 1.66/0.99  smt_new_axioms:                         0
% 1.66/0.99  pred_elim_cands:                        3
% 1.66/0.99  pred_elim:                              4
% 1.66/0.99  pred_elim_cl:                           8
% 1.66/0.99  pred_elim_cycles:                       8
% 1.66/0.99  merged_defs:                            0
% 1.66/0.99  merged_defs_ncl:                        0
% 1.66/0.99  bin_hyper_res:                          0
% 1.66/0.99  prep_cycles:                            4
% 1.66/0.99  pred_elim_time:                         0.009
% 1.66/0.99  splitting_time:                         0.
% 1.66/0.99  sem_filter_time:                        0.
% 1.66/0.99  monotx_time:                            0.
% 1.66/0.99  subtype_inf_time:                       0.
% 1.66/0.99  
% 1.66/0.99  ------ Problem properties
% 1.66/0.99  
% 1.66/0.99  clauses:                                16
% 1.66/0.99  conjectures:                            2
% 1.66/0.99  epr:                                    1
% 1.66/0.99  horn:                                   15
% 1.66/0.99  ground:                                 5
% 1.66/0.99  unary:                                  4
% 1.66/0.99  binary:                                 6
% 1.66/0.99  lits:                                   35
% 1.66/0.99  lits_eq:                                19
% 1.66/0.99  fd_pure:                                0
% 1.66/0.99  fd_pseudo:                              0
% 1.66/0.99  fd_cond:                                0
% 1.66/0.99  fd_pseudo_cond:                         0
% 1.66/0.99  ac_symbols:                             0
% 1.66/0.99  
% 1.66/0.99  ------ Propositional Solver
% 1.66/0.99  
% 1.66/0.99  prop_solver_calls:                      29
% 1.66/0.99  prop_fast_solver_calls:                 666
% 1.66/0.99  smt_solver_calls:                       0
% 1.66/0.99  smt_fast_solver_calls:                  0
% 1.66/0.99  prop_num_of_clauses:                    528
% 1.66/0.99  prop_preprocess_simplified:             2973
% 1.66/0.99  prop_fo_subsumed:                       8
% 1.66/0.99  prop_solver_time:                       0.
% 1.66/0.99  smt_solver_time:                        0.
% 1.66/0.99  smt_fast_solver_time:                   0.
% 1.66/0.99  prop_fast_solver_time:                  0.
% 1.66/0.99  prop_unsat_core_time:                   0.
% 1.66/0.99  
% 1.66/0.99  ------ QBF
% 1.66/0.99  
% 1.66/0.99  qbf_q_res:                              0
% 1.66/0.99  qbf_num_tautologies:                    0
% 1.66/0.99  qbf_prep_cycles:                        0
% 1.66/0.99  
% 1.66/0.99  ------ BMC1
% 1.66/0.99  
% 1.66/0.99  bmc1_current_bound:                     -1
% 1.66/0.99  bmc1_last_solved_bound:                 -1
% 1.66/0.99  bmc1_unsat_core_size:                   -1
% 1.66/0.99  bmc1_unsat_core_parents_size:           -1
% 1.66/0.99  bmc1_merge_next_fun:                    0
% 1.66/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.66/0.99  
% 1.66/0.99  ------ Instantiation
% 1.66/0.99  
% 1.66/0.99  inst_num_of_clauses:                    208
% 1.66/0.99  inst_num_in_passive:                    43
% 1.66/0.99  inst_num_in_active:                     152
% 1.66/0.99  inst_num_in_unprocessed:                13
% 1.66/0.99  inst_num_of_loops:                      160
% 1.66/0.99  inst_num_of_learning_restarts:          0
% 1.66/0.99  inst_num_moves_active_passive:          3
% 1.66/0.99  inst_lit_activity:                      0
% 1.66/0.99  inst_lit_activity_moves:                0
% 1.66/0.99  inst_num_tautologies:                   0
% 1.66/0.99  inst_num_prop_implied:                  0
% 1.66/0.99  inst_num_existing_simplified:           0
% 1.66/0.99  inst_num_eq_res_simplified:             0
% 1.66/0.99  inst_num_child_elim:                    0
% 1.66/0.99  inst_num_of_dismatching_blockings:      40
% 1.66/0.99  inst_num_of_non_proper_insts:           235
% 1.66/0.99  inst_num_of_duplicates:                 0
% 1.66/0.99  inst_inst_num_from_inst_to_res:         0
% 1.66/0.99  inst_dismatching_checking_time:         0.
% 1.66/0.99  
% 1.66/0.99  ------ Resolution
% 1.66/0.99  
% 1.66/0.99  res_num_of_clauses:                     0
% 1.66/0.99  res_num_in_passive:                     0
% 1.66/0.99  res_num_in_active:                      0
% 1.66/0.99  res_num_of_loops:                       113
% 1.66/0.99  res_forward_subset_subsumed:            86
% 1.66/0.99  res_backward_subset_subsumed:           0
% 1.66/0.99  res_forward_subsumed:                   0
% 1.66/0.99  res_backward_subsumed:                  0
% 1.66/0.99  res_forward_subsumption_resolution:     0
% 1.66/0.99  res_backward_subsumption_resolution:    0
% 1.66/0.99  res_clause_to_clause_subsumption:       45
% 1.66/0.99  res_orphan_elimination:                 0
% 1.66/0.99  res_tautology_del:                      60
% 1.66/0.99  res_num_eq_res_simplified:              1
% 1.66/0.99  res_num_sel_changes:                    0
% 1.66/0.99  res_moves_from_active_to_pass:          0
% 1.66/0.99  
% 1.66/0.99  ------ Superposition
% 1.66/0.99  
% 1.66/0.99  sup_time_total:                         0.
% 1.66/0.99  sup_time_generating:                    0.
% 1.66/0.99  sup_time_sim_full:                      0.
% 1.66/0.99  sup_time_sim_immed:                     0.
% 1.66/0.99  
% 1.66/0.99  sup_num_of_clauses:                     29
% 1.66/0.99  sup_num_in_active:                      26
% 1.66/0.99  sup_num_in_passive:                     3
% 1.66/0.99  sup_num_of_loops:                       31
% 1.66/0.99  sup_fw_superposition:                   7
% 1.66/0.99  sup_bw_superposition:                   6
% 1.66/0.99  sup_immediate_simplified:               2
% 1.66/0.99  sup_given_eliminated:                   0
% 1.66/0.99  comparisons_done:                       0
% 1.66/0.99  comparisons_avoided:                    0
% 1.66/0.99  
% 1.66/0.99  ------ Simplifications
% 1.66/0.99  
% 1.66/0.99  
% 1.66/0.99  sim_fw_subset_subsumed:                 0
% 1.66/0.99  sim_bw_subset_subsumed:                 0
% 1.66/0.99  sim_fw_subsumed:                        0
% 1.66/0.99  sim_bw_subsumed:                        0
% 1.66/0.99  sim_fw_subsumption_res:                 0
% 1.66/0.99  sim_bw_subsumption_res:                 0
% 1.66/0.99  sim_tautology_del:                      2
% 1.66/0.99  sim_eq_tautology_del:                   0
% 1.66/0.99  sim_eq_res_simp:                        0
% 1.66/0.99  sim_fw_demodulated:                     0
% 1.66/0.99  sim_bw_demodulated:                     6
% 1.66/0.99  sim_light_normalised:                   4
% 1.66/0.99  sim_joinable_taut:                      0
% 1.66/0.99  sim_joinable_simp:                      0
% 1.66/0.99  sim_ac_normalised:                      0
% 1.66/0.99  sim_smt_subsumption:                    0
% 1.66/0.99  
%------------------------------------------------------------------------------
