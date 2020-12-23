%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:27 EST 2020

% Result     : Theorem 11.82s
% Output     : CNFRefutation 11.82s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 818 expanded)
%              Number of clauses        :   77 ( 199 expanded)
%              Number of leaves         :   18 ( 190 expanded)
%              Depth                    :   30
%              Number of atoms          :  405 (2473 expanded)
%              Number of equality atoms :  269 (1384 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f32,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f39,plain,
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

fof(f40,plain,
    ( k1_tarski(k1_funct_1(sK2,sK0)) != k2_relset_1(k1_tarski(sK0),sK1,sK2)
    & k1_xboole_0 != sK1
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_2(sK2,k1_tarski(sK0),sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f32,f39])).

fof(f69,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f73,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f42,f43])).

fof(f74,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f41,f73])).

fof(f83,plain,(
    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f69,f74])).

fof(f16,axiom,(
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

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f70,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f40])).

fof(f82,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f70,f74])).

fof(f71,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f40])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f52,f74])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f54,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k1_relat_1(X1))
          | k1_xboole_0 = k11_relat_1(X1,X0) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X1))
      | k1_xboole_0 = k11_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f59,f74])).

fof(f68,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f72,plain,(
    k1_tarski(k1_funct_1(sK2,sK0)) != k2_relset_1(k1_tarski(sK0),sK1,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f81,plain,(
    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) ),
    inference(definition_unfolding,[],[f72,f74,f74])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f58,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
     => ( k2_zfmisc_1(X0,k1_tarski(X1)) != k1_xboole_0
        & k2_zfmisc_1(k1_tarski(X1),X0) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,k1_tarski(X1)) != k1_xboole_0
        & k2_zfmisc_1(k1_tarski(X1),X0) != k1_xboole_0 )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(k1_tarski(X1),X0) != k1_xboole_0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X0) != k1_xboole_0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f47,f74])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f33])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f85,plain,(
    ! [X1] : k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(equality_resolution,[],[f45])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f89,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f66])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_309,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_26])).

cnf(c_310,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | k1_relset_1(X0,X1,sK2) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_309])).

cnf(c_472,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != X0
    | k1_relset_1(X0,X1,sK2) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK1 != X1
    | sK2 != sK2
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_310])).

cnf(c_473,plain,
    ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_472])).

cnf(c_25,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_474,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_473,c_25])).

cnf(c_475,plain,
    ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    inference(renaming,[status(thm)],[c_474])).

cnf(c_531,plain,
    ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(equality_resolution_simp,[status(thm)],[c_475])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_354,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_26])).

cnf(c_355,plain,
    ( k1_relset_1(X0,X1,sK2) = k1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_354])).

cnf(c_51514,plain,
    ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k1_relat_1(sK2) ),
    inference(equality_resolution,[status(thm)],[c_355])).

cnf(c_51520,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_531,c_51514])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_294,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_26])).

cnf(c_295,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_294])).

cnf(c_51425,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_295])).

cnf(c_51575,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)) != k1_zfmisc_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_51425,c_51520])).

cnf(c_51582,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_51575])).

cnf(c_9,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_51429,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_51634,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_51582,c_51429])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_51430,plain,
    ( k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_51692,plain,
    ( k9_relat_1(sK2,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_51634,c_51430])).

cnf(c_51743,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) = k11_relat_1(sK2,sK0) ),
    inference(superposition,[status(thm)],[c_51520,c_51692])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_51428,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_51636,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_51634,c_51428])).

cnf(c_51750,plain,
    ( k11_relat_1(sK2,sK0) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_51743,c_51636])).

cnf(c_11,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k11_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_247,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_28])).

cnf(c_248,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | k2_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)) = k11_relat_1(sK2,X0) ),
    inference(unflattening,[status(thm)],[c_247])).

cnf(c_267,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK2)
    | X1 != X2
    | k2_enumset1(k1_funct_1(sK2,X1),k1_funct_1(sK2,X1),k1_funct_1(sK2,X1),k1_funct_1(sK2,X1)) = k11_relat_1(sK2,X1)
    | k11_relat_1(X0,X2) = k1_xboole_0
    | k1_relat_1(X0) != k1_relat_1(sK2) ),
    inference(resolution_lifted,[status(thm)],[c_11,c_248])).

cnf(c_268,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK2)
    | k2_enumset1(k1_funct_1(sK2,X1),k1_funct_1(sK2,X1),k1_funct_1(sK2,X1),k1_funct_1(sK2,X1)) = k11_relat_1(sK2,X1)
    | k11_relat_1(X0,X1) = k1_xboole_0
    | k1_relat_1(X0) != k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_267])).

cnf(c_51426,plain,
    ( k2_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)) = k11_relat_1(sK2,X0)
    | k11_relat_1(X1,X0) = k1_xboole_0
    | k1_relat_1(X1) != k1_relat_1(sK2)
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_268])).

cnf(c_51601,plain,
    ( k2_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)) = k11_relat_1(sK2,X0)
    | k11_relat_1(sK2,X0) = k1_xboole_0
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_51426])).

cnf(c_51639,plain,
    ( k11_relat_1(sK2,X0) = k1_xboole_0
    | k2_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)) = k11_relat_1(sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_51601,c_51634])).

cnf(c_51640,plain,
    ( k2_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)) = k11_relat_1(sK2,X0)
    | k11_relat_1(sK2,X0) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_51639])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_345,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_26])).

cnf(c_346,plain,
    ( k2_relset_1(X0,X1,sK2) = k2_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_345])).

cnf(c_51503,plain,
    ( k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2) ),
    inference(equality_resolution,[status(thm)],[c_346])).

cnf(c_24,negated_conjecture,
    ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_51516,plain,
    ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_51503,c_24])).

cnf(c_51645,plain,
    ( k11_relat_1(sK2,sK0) != k2_relat_1(sK2)
    | k11_relat_1(sK2,sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_51640,c_51516])).

cnf(c_51757,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | k2_relat_1(sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_51750,c_51645])).

cnf(c_51768,plain,
    ( k2_relat_1(sK2) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_51757])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_51427,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_51794,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_51768,c_51427])).

cnf(c_51841,plain,
    ( k1_relat_1(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_51794,c_51634])).

cnf(c_4,plain,
    ( k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),X1) != k1_xboole_0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_51549,plain,
    ( k2_zfmisc_1(k1_relat_1(sK2),X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_51520,c_4])).

cnf(c_51850,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(demodulation,[status(thm)],[c_51841,c_51549])).

cnf(c_1,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_51883,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_51850,c_1])).

cnf(c_51884,plain,
    ( k1_xboole_0 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_51883])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_380,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))
    | sK2 != X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_26])).

cnf(c_381,plain,
    ( ~ v1_funct_2(sK2,X0,k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_380])).

cnf(c_482,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != X0
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))
    | sK1 != k1_xboole_0
    | sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_381])).

cnf(c_483,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0))
    | sK1 != k1_xboole_0
    | sK2 = k1_xboole_0
    | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(unflattening,[status(thm)],[c_482])).

cnf(c_2,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_85,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_86,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_586,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_8057,plain,
    ( X0 = sK1
    | X0 != k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_586])).

cnf(c_8058,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8057])).

cnf(c_51395,plain,
    ( sK1 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_483,c_25,c_85,c_86,c_8058])).

cnf(c_51943,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_51884,c_51395])).

cnf(c_51948,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_51943])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:03:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.82/1.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.82/1.99  
% 11.82/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.82/1.99  
% 11.82/1.99  ------  iProver source info
% 11.82/1.99  
% 11.82/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.82/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.82/1.99  git: non_committed_changes: false
% 11.82/1.99  git: last_make_outside_of_git: false
% 11.82/1.99  
% 11.82/1.99  ------ 
% 11.82/1.99  ------ Parsing...
% 11.82/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.82/1.99  ------ Proving...
% 11.82/1.99  ------ Problem Properties 
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  clauses                                 21
% 11.82/1.99  conjectures                             3
% 11.82/1.99  EPR                                     1
% 11.82/1.99  Horn                                    17
% 11.82/1.99  unary                                   7
% 11.82/1.99  binary                                  7
% 11.82/1.99  lits                                    45
% 11.82/1.99  lits eq                                 36
% 11.82/1.99  fd_pure                                 0
% 11.82/1.99  fd_pseudo                               0
% 11.82/1.99  fd_cond                                 3
% 11.82/1.99  fd_pseudo_cond                          1
% 11.82/1.99  AC symbols                              0
% 11.82/1.99  
% 11.82/1.99  ------ Input Options Time Limit: Unbounded
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 11.82/1.99  Current options:
% 11.82/1.99  ------ 
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ Proving...
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.82/1.99  
% 11.82/1.99  ------ Proving...
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.82/1.99  
% 11.82/1.99  ------ Proving...
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.82/1.99  
% 11.82/1.99  ------ Proving...
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.82/1.99  
% 11.82/1.99  ------ Proving...
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.82/1.99  
% 11.82/1.99  ------ Proving...
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.82/1.99  
% 11.82/1.99  ------ Proving...
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.82/1.99  
% 11.82/1.99  ------ Proving...
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.82/1.99  
% 11.82/1.99  ------ Proving...
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.82/1.99  
% 11.82/1.99  ------ Proving...
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.82/1.99  
% 11.82/1.99  ------ Proving...
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.82/1.99  
% 11.82/1.99  ------ Proving...
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.82/1.99  
% 11.82/1.99  ------ Proving...
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.82/1.99  
% 11.82/1.99  ------ Proving...
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.82/1.99  
% 11.82/1.99  ------ Proving...
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.82/1.99  
% 11.82/1.99  ------ Proving...
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.82/1.99  
% 11.82/1.99  ------ Proving...
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.82/1.99  
% 11.82/1.99  ------ Proving...
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.82/1.99  
% 11.82/1.99  ------ Proving...
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.82/1.99  
% 11.82/1.99  ------ Proving...
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.82/1.99  
% 11.82/1.99  ------ Proving...
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.82/1.99  
% 11.82/1.99  ------ Proving...
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.82/1.99  
% 11.82/1.99  ------ Proving...
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.82/1.99  
% 11.82/1.99  ------ Proving...
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.82/1.99  
% 11.82/1.99  ------ Proving...
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.82/1.99  
% 11.82/1.99  ------ Proving...
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.82/1.99  
% 11.82/1.99  ------ Proving...
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.82/1.99  
% 11.82/1.99  ------ Proving...
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.82/1.99  
% 11.82/1.99  ------ Proving...
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.82/1.99  
% 11.82/1.99  ------ Proving...
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.82/1.99  
% 11.82/1.99  ------ Proving...
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.82/1.99  
% 11.82/1.99  ------ Proving...
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.82/1.99  
% 11.82/1.99  ------ Proving...
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.82/1.99  
% 11.82/1.99  ------ Proving...
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.82/1.99  
% 11.82/1.99  ------ Proving...
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.82/1.99  
% 11.82/1.99  ------ Proving...
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.82/1.99  
% 11.82/1.99  ------ Proving...
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.82/1.99  
% 11.82/1.99  ------ Proving...
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.82/1.99  
% 11.82/1.99  ------ Proving...
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.82/1.99  
% 11.82/1.99  ------ Proving...
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.82/1.99  
% 11.82/1.99  ------ Proving...
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.82/1.99  
% 11.82/1.99  ------ Proving...
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.82/1.99  
% 11.82/1.99  ------ Proving...
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.82/1.99  
% 11.82/1.99  ------ Proving...
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.82/1.99  
% 11.82/1.99  ------ Proving...
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.82/1.99  
% 11.82/1.99  ------ Proving...
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.82/1.99  
% 11.82/1.99  ------ Proving...
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.82/1.99  
% 11.82/1.99  ------ Proving...
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.82/1.99  
% 11.82/1.99  ------ Proving...
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.82/1.99  
% 11.82/1.99  ------ Proving...
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.82/1.99  
% 11.82/1.99  ------ Proving...
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.82/1.99  
% 11.82/1.99  ------ Proving...
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.82/1.99  
% 11.82/1.99  ------ Proving...
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.82/1.99  
% 11.82/1.99  ------ Proving...
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.82/1.99  
% 11.82/1.99  ------ Proving...
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.82/1.99  
% 11.82/1.99  ------ Proving...
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.82/1.99  
% 11.82/1.99  ------ Proving...
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  % SZS status Theorem for theBenchmark.p
% 11.82/1.99  
% 11.82/1.99   Resolution empty clause
% 11.82/1.99  
% 11.82/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.82/1.99  
% 11.82/1.99  fof(f17,conjecture,(
% 11.82/1.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 11.82/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.82/1.99  
% 11.82/1.99  fof(f18,negated_conjecture,(
% 11.82/1.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 11.82/1.99    inference(negated_conjecture,[],[f17])).
% 11.82/1.99  
% 11.82/1.99  fof(f31,plain,(
% 11.82/1.99    ? [X0,X1,X2] : ((k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 11.82/1.99    inference(ennf_transformation,[],[f18])).
% 11.82/1.99  
% 11.82/1.99  fof(f32,plain,(
% 11.82/1.99    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 11.82/1.99    inference(flattening,[],[f31])).
% 11.82/1.99  
% 11.82/1.99  fof(f39,plain,(
% 11.82/1.99    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_tarski(k1_funct_1(sK2,sK0)) != k2_relset_1(k1_tarski(sK0),sK1,sK2) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2))),
% 11.82/1.99    introduced(choice_axiom,[])).
% 11.82/1.99  
% 11.82/1.99  fof(f40,plain,(
% 11.82/1.99    k1_tarski(k1_funct_1(sK2,sK0)) != k2_relset_1(k1_tarski(sK0),sK1,sK2) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2)),
% 11.82/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f32,f39])).
% 11.82/1.99  
% 11.82/1.99  fof(f69,plain,(
% 11.82/1.99    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 11.82/1.99    inference(cnf_transformation,[],[f40])).
% 11.82/1.99  
% 11.82/1.99  fof(f1,axiom,(
% 11.82/1.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 11.82/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.82/1.99  
% 11.82/1.99  fof(f41,plain,(
% 11.82/1.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 11.82/1.99    inference(cnf_transformation,[],[f1])).
% 11.82/1.99  
% 11.82/1.99  fof(f2,axiom,(
% 11.82/1.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 11.82/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.82/1.99  
% 11.82/1.99  fof(f42,plain,(
% 11.82/1.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 11.82/1.99    inference(cnf_transformation,[],[f2])).
% 11.82/1.99  
% 11.82/1.99  fof(f3,axiom,(
% 11.82/1.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 11.82/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.82/1.99  
% 11.82/1.99  fof(f43,plain,(
% 11.82/1.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 11.82/1.99    inference(cnf_transformation,[],[f3])).
% 11.82/1.99  
% 11.82/1.99  fof(f73,plain,(
% 11.82/1.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 11.82/1.99    inference(definition_unfolding,[],[f42,f43])).
% 11.82/1.99  
% 11.82/1.99  fof(f74,plain,(
% 11.82/1.99    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 11.82/1.99    inference(definition_unfolding,[],[f41,f73])).
% 11.82/1.99  
% 11.82/1.99  fof(f83,plain,(
% 11.82/1.99    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 11.82/1.99    inference(definition_unfolding,[],[f69,f74])).
% 11.82/1.99  
% 11.82/1.99  fof(f16,axiom,(
% 11.82/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 11.82/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.82/1.99  
% 11.82/1.99  fof(f29,plain,(
% 11.82/1.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.82/1.99    inference(ennf_transformation,[],[f16])).
% 11.82/1.99  
% 11.82/1.99  fof(f30,plain,(
% 11.82/1.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.82/1.99    inference(flattening,[],[f29])).
% 11.82/1.99  
% 11.82/1.99  fof(f38,plain,(
% 11.82/1.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.82/1.99    inference(nnf_transformation,[],[f30])).
% 11.82/1.99  
% 11.82/1.99  fof(f62,plain,(
% 11.82/1.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.82/1.99    inference(cnf_transformation,[],[f38])).
% 11.82/1.99  
% 11.82/1.99  fof(f70,plain,(
% 11.82/1.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 11.82/1.99    inference(cnf_transformation,[],[f40])).
% 11.82/1.99  
% 11.82/1.99  fof(f82,plain,(
% 11.82/1.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 11.82/1.99    inference(definition_unfolding,[],[f70,f74])).
% 11.82/1.99  
% 11.82/1.99  fof(f71,plain,(
% 11.82/1.99    k1_xboole_0 != sK1),
% 11.82/1.99    inference(cnf_transformation,[],[f40])).
% 11.82/1.99  
% 11.82/1.99  fof(f14,axiom,(
% 11.82/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 11.82/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.82/1.99  
% 11.82/1.99  fof(f27,plain,(
% 11.82/1.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.82/1.99    inference(ennf_transformation,[],[f14])).
% 11.82/1.99  
% 11.82/1.99  fof(f60,plain,(
% 11.82/1.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.82/1.99    inference(cnf_transformation,[],[f27])).
% 11.82/1.99  
% 11.82/1.99  fof(f7,axiom,(
% 11.82/1.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 11.82/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.82/1.99  
% 11.82/1.99  fof(f20,plain,(
% 11.82/1.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 11.82/1.99    inference(ennf_transformation,[],[f7])).
% 11.82/1.99  
% 11.82/1.99  fof(f51,plain,(
% 11.82/1.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 11.82/1.99    inference(cnf_transformation,[],[f20])).
% 11.82/1.99  
% 11.82/1.99  fof(f9,axiom,(
% 11.82/1.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 11.82/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.82/1.99  
% 11.82/1.99  fof(f53,plain,(
% 11.82/1.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 11.82/1.99    inference(cnf_transformation,[],[f9])).
% 11.82/1.99  
% 11.82/1.99  fof(f8,axiom,(
% 11.82/1.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 11.82/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.82/1.99  
% 11.82/1.99  fof(f21,plain,(
% 11.82/1.99    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 11.82/1.99    inference(ennf_transformation,[],[f8])).
% 11.82/1.99  
% 11.82/1.99  fof(f52,plain,(
% 11.82/1.99    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 11.82/1.99    inference(cnf_transformation,[],[f21])).
% 11.82/1.99  
% 11.82/1.99  fof(f79,plain,(
% 11.82/1.99    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 11.82/1.99    inference(definition_unfolding,[],[f52,f74])).
% 11.82/1.99  
% 11.82/1.99  fof(f10,axiom,(
% 11.82/1.99    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 11.82/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.82/1.99  
% 11.82/1.99  fof(f22,plain,(
% 11.82/1.99    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 11.82/1.99    inference(ennf_transformation,[],[f10])).
% 11.82/1.99  
% 11.82/1.99  fof(f54,plain,(
% 11.82/1.99    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 11.82/1.99    inference(cnf_transformation,[],[f22])).
% 11.82/1.99  
% 11.82/1.99  fof(f11,axiom,(
% 11.82/1.99    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 11.82/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.82/1.99  
% 11.82/1.99  fof(f23,plain,(
% 11.82/1.99    ! [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 11.82/1.99    inference(ennf_transformation,[],[f11])).
% 11.82/1.99  
% 11.82/1.99  fof(f36,plain,(
% 11.82/1.99    ! [X0,X1] : (((r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0)) & (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)))) | ~v1_relat_1(X1))),
% 11.82/1.99    inference(nnf_transformation,[],[f23])).
% 11.82/1.99  
% 11.82/1.99  fof(f56,plain,(
% 11.82/1.99    ( ! [X0,X1] : (r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.82/1.99    inference(cnf_transformation,[],[f36])).
% 11.82/1.99  
% 11.82/1.99  fof(f13,axiom,(
% 11.82/1.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)))),
% 11.82/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.82/1.99  
% 11.82/1.99  fof(f25,plain,(
% 11.82/1.99    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 11.82/1.99    inference(ennf_transformation,[],[f13])).
% 11.82/1.99  
% 11.82/1.99  fof(f26,plain,(
% 11.82/1.99    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 11.82/1.99    inference(flattening,[],[f25])).
% 11.82/1.99  
% 11.82/1.99  fof(f59,plain,(
% 11.82/1.99    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 11.82/1.99    inference(cnf_transformation,[],[f26])).
% 11.82/1.99  
% 11.82/1.99  fof(f80,plain,(
% 11.82/1.99    ( ! [X0,X1] : (k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 11.82/1.99    inference(definition_unfolding,[],[f59,f74])).
% 11.82/1.99  
% 11.82/1.99  fof(f68,plain,(
% 11.82/1.99    v1_funct_1(sK2)),
% 11.82/1.99    inference(cnf_transformation,[],[f40])).
% 11.82/1.99  
% 11.82/1.99  fof(f15,axiom,(
% 11.82/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 11.82/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.82/1.99  
% 11.82/1.99  fof(f28,plain,(
% 11.82/1.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.82/1.99    inference(ennf_transformation,[],[f15])).
% 11.82/1.99  
% 11.82/1.99  fof(f61,plain,(
% 11.82/1.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.82/1.99    inference(cnf_transformation,[],[f28])).
% 11.82/1.99  
% 11.82/1.99  fof(f72,plain,(
% 11.82/1.99    k1_tarski(k1_funct_1(sK2,sK0)) != k2_relset_1(k1_tarski(sK0),sK1,sK2)),
% 11.82/1.99    inference(cnf_transformation,[],[f40])).
% 11.82/1.99  
% 11.82/1.99  fof(f81,plain,(
% 11.82/1.99    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)),
% 11.82/1.99    inference(definition_unfolding,[],[f72,f74,f74])).
% 11.82/1.99  
% 11.82/1.99  fof(f12,axiom,(
% 11.82/1.99    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 11.82/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.82/1.99  
% 11.82/1.99  fof(f24,plain,(
% 11.82/1.99    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 11.82/1.99    inference(ennf_transformation,[],[f12])).
% 11.82/1.99  
% 11.82/1.99  fof(f37,plain,(
% 11.82/1.99    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 11.82/1.99    inference(nnf_transformation,[],[f24])).
% 11.82/1.99  
% 11.82/1.99  fof(f58,plain,(
% 11.82/1.99    ( ! [X0] : (k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 11.82/1.99    inference(cnf_transformation,[],[f37])).
% 11.82/1.99  
% 11.82/1.99  fof(f5,axiom,(
% 11.82/1.99    ! [X0,X1] : (k1_xboole_0 != X0 => (k2_zfmisc_1(X0,k1_tarski(X1)) != k1_xboole_0 & k2_zfmisc_1(k1_tarski(X1),X0) != k1_xboole_0))),
% 11.82/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.82/1.99  
% 11.82/1.99  fof(f19,plain,(
% 11.82/1.99    ! [X0,X1] : ((k2_zfmisc_1(X0,k1_tarski(X1)) != k1_xboole_0 & k2_zfmisc_1(k1_tarski(X1),X0) != k1_xboole_0) | k1_xboole_0 = X0)),
% 11.82/1.99    inference(ennf_transformation,[],[f5])).
% 11.82/1.99  
% 11.82/1.99  fof(f47,plain,(
% 11.82/1.99    ( ! [X0,X1] : (k2_zfmisc_1(k1_tarski(X1),X0) != k1_xboole_0 | k1_xboole_0 = X0) )),
% 11.82/1.99    inference(cnf_transformation,[],[f19])).
% 11.82/1.99  
% 11.82/1.99  fof(f76,plain,(
% 11.82/1.99    ( ! [X0,X1] : (k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X0) != k1_xboole_0 | k1_xboole_0 = X0) )),
% 11.82/1.99    inference(definition_unfolding,[],[f47,f74])).
% 11.82/1.99  
% 11.82/1.99  fof(f4,axiom,(
% 11.82/1.99    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 11.82/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.82/1.99  
% 11.82/1.99  fof(f33,plain,(
% 11.82/1.99    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 11.82/1.99    inference(nnf_transformation,[],[f4])).
% 11.82/1.99  
% 11.82/1.99  fof(f34,plain,(
% 11.82/1.99    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 11.82/1.99    inference(flattening,[],[f33])).
% 11.82/1.99  
% 11.82/1.99  fof(f45,plain,(
% 11.82/1.99    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 11.82/1.99    inference(cnf_transformation,[],[f34])).
% 11.82/1.99  
% 11.82/1.99  fof(f85,plain,(
% 11.82/1.99    ( ! [X1] : (k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0) )),
% 11.82/1.99    inference(equality_resolution,[],[f45])).
% 11.82/1.99  
% 11.82/1.99  fof(f66,plain,(
% 11.82/1.99    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.82/1.99    inference(cnf_transformation,[],[f38])).
% 11.82/1.99  
% 11.82/1.99  fof(f89,plain,(
% 11.82/1.99    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 11.82/1.99    inference(equality_resolution,[],[f66])).
% 11.82/1.99  
% 11.82/1.99  fof(f44,plain,(
% 11.82/1.99    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0) )),
% 11.82/1.99    inference(cnf_transformation,[],[f34])).
% 11.82/1.99  
% 11.82/1.99  cnf(c_27,negated_conjecture,
% 11.82/1.99      ( v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
% 11.82/1.99      inference(cnf_transformation,[],[f83]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_23,plain,
% 11.82/1.99      ( ~ v1_funct_2(X0,X1,X2)
% 11.82/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.82/1.99      | k1_relset_1(X1,X2,X0) = X1
% 11.82/1.99      | k1_xboole_0 = X2 ),
% 11.82/1.99      inference(cnf_transformation,[],[f62]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_26,negated_conjecture,
% 11.82/1.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
% 11.82/1.99      inference(cnf_transformation,[],[f82]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_309,plain,
% 11.82/1.99      ( ~ v1_funct_2(X0,X1,X2)
% 11.82/1.99      | k1_relset_1(X1,X2,X0) = X1
% 11.82/1.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 11.82/1.99      | sK2 != X0
% 11.82/1.99      | k1_xboole_0 = X2 ),
% 11.82/1.99      inference(resolution_lifted,[status(thm)],[c_23,c_26]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_310,plain,
% 11.82/1.99      ( ~ v1_funct_2(sK2,X0,X1)
% 11.82/1.99      | k1_relset_1(X0,X1,sK2) = X0
% 11.82/1.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 11.82/1.99      | k1_xboole_0 = X1 ),
% 11.82/1.99      inference(unflattening,[status(thm)],[c_309]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_472,plain,
% 11.82/1.99      ( k2_enumset1(sK0,sK0,sK0,sK0) != X0
% 11.82/1.99      | k1_relset_1(X0,X1,sK2) = X0
% 11.82/1.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 11.82/1.99      | sK1 != X1
% 11.82/1.99      | sK2 != sK2
% 11.82/1.99      | k1_xboole_0 = X1 ),
% 11.82/1.99      inference(resolution_lifted,[status(thm)],[c_27,c_310]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_473,plain,
% 11.82/1.99      ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0)
% 11.82/1.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
% 11.82/1.99      | k1_xboole_0 = sK1 ),
% 11.82/1.99      inference(unflattening,[status(thm)],[c_472]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_25,negated_conjecture,
% 11.82/1.99      ( k1_xboole_0 != sK1 ),
% 11.82/1.99      inference(cnf_transformation,[],[f71]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_474,plain,
% 11.82/1.99      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
% 11.82/1.99      | k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0) ),
% 11.82/1.99      inference(global_propositional_subsumption,[status(thm)],[c_473,c_25]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_475,plain,
% 11.82/1.99      ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0)
% 11.82/1.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
% 11.82/1.99      inference(renaming,[status(thm)],[c_474]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_531,plain,
% 11.82/1.99      ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0) ),
% 11.82/1.99      inference(equality_resolution_simp,[status(thm)],[c_475]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_16,plain,
% 11.82/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.82/1.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 11.82/1.99      inference(cnf_transformation,[],[f60]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_354,plain,
% 11.82/1.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 11.82/1.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 11.82/1.99      | sK2 != X2 ),
% 11.82/1.99      inference(resolution_lifted,[status(thm)],[c_16,c_26]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_355,plain,
% 11.82/1.99      ( k1_relset_1(X0,X1,sK2) = k1_relat_1(sK2)
% 11.82/1.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 11.82/1.99      inference(unflattening,[status(thm)],[c_354]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_51514,plain,
% 11.82/1.99      ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k1_relat_1(sK2) ),
% 11.82/1.99      inference(equality_resolution,[status(thm)],[c_355]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_51520,plain,
% 11.82/1.99      ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) ),
% 11.82/1.99      inference(light_normalisation,[status(thm)],[c_531,c_51514]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_7,plain,
% 11.82/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 11.82/1.99      inference(cnf_transformation,[],[f51]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_294,plain,
% 11.82/1.99      ( ~ v1_relat_1(X0)
% 11.82/1.99      | v1_relat_1(X1)
% 11.82/1.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(X0)
% 11.82/1.99      | sK2 != X1 ),
% 11.82/1.99      inference(resolution_lifted,[status(thm)],[c_7,c_26]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_295,plain,
% 11.82/1.99      ( ~ v1_relat_1(X0)
% 11.82/1.99      | v1_relat_1(sK2)
% 11.82/1.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(X0) ),
% 11.82/1.99      inference(unflattening,[status(thm)],[c_294]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_51425,plain,
% 11.82/1.99      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(X0)
% 11.82/1.99      | v1_relat_1(X0) != iProver_top
% 11.82/1.99      | v1_relat_1(sK2) = iProver_top ),
% 11.82/1.99      inference(predicate_to_equality,[status(thm)],[c_295]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_51575,plain,
% 11.82/1.99      ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)) != k1_zfmisc_1(X0)
% 11.82/1.99      | v1_relat_1(X0) != iProver_top
% 11.82/1.99      | v1_relat_1(sK2) = iProver_top ),
% 11.82/1.99      inference(light_normalisation,[status(thm)],[c_51425,c_51520]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_51582,plain,
% 11.82/1.99      ( v1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)) != iProver_top
% 11.82/1.99      | v1_relat_1(sK2) = iProver_top ),
% 11.82/1.99      inference(equality_resolution,[status(thm)],[c_51575]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_9,plain,
% 11.82/1.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 11.82/1.99      inference(cnf_transformation,[],[f53]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_51429,plain,
% 11.82/1.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 11.82/1.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_51634,plain,
% 11.82/1.99      ( v1_relat_1(sK2) = iProver_top ),
% 11.82/1.99      inference(forward_subsumption_resolution,[status(thm)],[c_51582,c_51429]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_8,plain,
% 11.82/1.99      ( ~ v1_relat_1(X0)
% 11.82/1.99      | k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
% 11.82/1.99      inference(cnf_transformation,[],[f79]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_51430,plain,
% 11.82/1.99      ( k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1)
% 11.82/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.82/1.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_51692,plain,
% 11.82/1.99      ( k9_relat_1(sK2,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK2,X0) ),
% 11.82/1.99      inference(superposition,[status(thm)],[c_51634,c_51430]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_51743,plain,
% 11.82/1.99      ( k9_relat_1(sK2,k1_relat_1(sK2)) = k11_relat_1(sK2,sK0) ),
% 11.82/1.99      inference(superposition,[status(thm)],[c_51520,c_51692]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_10,plain,
% 11.82/1.99      ( ~ v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 11.82/1.99      inference(cnf_transformation,[],[f54]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_51428,plain,
% 11.82/1.99      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 11.82/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.82/1.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_51636,plain,
% 11.82/1.99      ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
% 11.82/1.99      inference(superposition,[status(thm)],[c_51634,c_51428]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_51750,plain,
% 11.82/1.99      ( k11_relat_1(sK2,sK0) = k2_relat_1(sK2) ),
% 11.82/1.99      inference(light_normalisation,[status(thm)],[c_51743,c_51636]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_11,plain,
% 11.82/1.99      ( r2_hidden(X0,k1_relat_1(X1))
% 11.82/1.99      | ~ v1_relat_1(X1)
% 11.82/1.99      | k11_relat_1(X1,X0) = k1_xboole_0 ),
% 11.82/1.99      inference(cnf_transformation,[],[f56]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_15,plain,
% 11.82/1.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 11.82/1.99      | ~ v1_funct_1(X1)
% 11.82/1.99      | ~ v1_relat_1(X1)
% 11.82/1.99      | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ),
% 11.82/1.99      inference(cnf_transformation,[],[f80]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_28,negated_conjecture,
% 11.82/1.99      ( v1_funct_1(sK2) ),
% 11.82/1.99      inference(cnf_transformation,[],[f68]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_247,plain,
% 11.82/1.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 11.82/1.99      | ~ v1_relat_1(X1)
% 11.82/1.99      | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
% 11.82/1.99      | sK2 != X1 ),
% 11.82/1.99      inference(resolution_lifted,[status(thm)],[c_15,c_28]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_248,plain,
% 11.82/1.99      ( ~ r2_hidden(X0,k1_relat_1(sK2))
% 11.82/1.99      | ~ v1_relat_1(sK2)
% 11.82/1.99      | k2_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)) = k11_relat_1(sK2,X0) ),
% 11.82/1.99      inference(unflattening,[status(thm)],[c_247]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_267,plain,
% 11.82/1.99      ( ~ v1_relat_1(X0)
% 11.82/1.99      | ~ v1_relat_1(sK2)
% 11.82/1.99      | X1 != X2
% 11.82/1.99      | k2_enumset1(k1_funct_1(sK2,X1),k1_funct_1(sK2,X1),k1_funct_1(sK2,X1),k1_funct_1(sK2,X1)) = k11_relat_1(sK2,X1)
% 11.82/1.99      | k11_relat_1(X0,X2) = k1_xboole_0
% 11.82/1.99      | k1_relat_1(X0) != k1_relat_1(sK2) ),
% 11.82/1.99      inference(resolution_lifted,[status(thm)],[c_11,c_248]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_268,plain,
% 11.82/1.99      ( ~ v1_relat_1(X0)
% 11.82/1.99      | ~ v1_relat_1(sK2)
% 11.82/1.99      | k2_enumset1(k1_funct_1(sK2,X1),k1_funct_1(sK2,X1),k1_funct_1(sK2,X1),k1_funct_1(sK2,X1)) = k11_relat_1(sK2,X1)
% 11.82/1.99      | k11_relat_1(X0,X1) = k1_xboole_0
% 11.82/1.99      | k1_relat_1(X0) != k1_relat_1(sK2) ),
% 11.82/1.99      inference(unflattening,[status(thm)],[c_267]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_51426,plain,
% 11.82/1.99      ( k2_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)) = k11_relat_1(sK2,X0)
% 11.82/1.99      | k11_relat_1(X1,X0) = k1_xboole_0
% 11.82/1.99      | k1_relat_1(X1) != k1_relat_1(sK2)
% 11.82/1.99      | v1_relat_1(X1) != iProver_top
% 11.82/1.99      | v1_relat_1(sK2) != iProver_top ),
% 11.82/1.99      inference(predicate_to_equality,[status(thm)],[c_268]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_51601,plain,
% 11.82/1.99      ( k2_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)) = k11_relat_1(sK2,X0)
% 11.82/1.99      | k11_relat_1(sK2,X0) = k1_xboole_0
% 11.82/1.99      | v1_relat_1(sK2) != iProver_top ),
% 11.82/1.99      inference(equality_resolution,[status(thm)],[c_51426]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_51639,plain,
% 11.82/1.99      ( k11_relat_1(sK2,X0) = k1_xboole_0
% 11.82/1.99      | k2_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)) = k11_relat_1(sK2,X0) ),
% 11.82/1.99      inference(global_propositional_subsumption,
% 11.82/1.99                [status(thm)],
% 11.82/1.99                [c_51601,c_51634]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_51640,plain,
% 11.82/1.99      ( k2_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)) = k11_relat_1(sK2,X0)
% 11.82/1.99      | k11_relat_1(sK2,X0) = k1_xboole_0 ),
% 11.82/1.99      inference(renaming,[status(thm)],[c_51639]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_17,plain,
% 11.82/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.82/1.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 11.82/1.99      inference(cnf_transformation,[],[f61]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_345,plain,
% 11.82/1.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 11.82/1.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 11.82/1.99      | sK2 != X2 ),
% 11.82/1.99      inference(resolution_lifted,[status(thm)],[c_17,c_26]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_346,plain,
% 11.82/1.99      ( k2_relset_1(X0,X1,sK2) = k2_relat_1(sK2)
% 11.82/1.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 11.82/1.99      inference(unflattening,[status(thm)],[c_345]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_51503,plain,
% 11.82/1.99      ( k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2) ),
% 11.82/1.99      inference(equality_resolution,[status(thm)],[c_346]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_24,negated_conjecture,
% 11.82/1.99      ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) ),
% 11.82/1.99      inference(cnf_transformation,[],[f81]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_51516,plain,
% 11.82/1.99      ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relat_1(sK2) ),
% 11.82/1.99      inference(demodulation,[status(thm)],[c_51503,c_24]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_51645,plain,
% 11.82/1.99      ( k11_relat_1(sK2,sK0) != k2_relat_1(sK2)
% 11.82/1.99      | k11_relat_1(sK2,sK0) = k1_xboole_0 ),
% 11.82/1.99      inference(superposition,[status(thm)],[c_51640,c_51516]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_51757,plain,
% 11.82/1.99      ( k2_relat_1(sK2) != k2_relat_1(sK2) | k2_relat_1(sK2) = k1_xboole_0 ),
% 11.82/1.99      inference(demodulation,[status(thm)],[c_51750,c_51645]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_51768,plain,
% 11.82/1.99      ( k2_relat_1(sK2) = k1_xboole_0 ),
% 11.82/1.99      inference(equality_resolution_simp,[status(thm)],[c_51757]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_13,plain,
% 11.82/1.99      ( ~ v1_relat_1(X0)
% 11.82/1.99      | k2_relat_1(X0) != k1_xboole_0
% 11.82/1.99      | k1_relat_1(X0) = k1_xboole_0 ),
% 11.82/1.99      inference(cnf_transformation,[],[f58]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_51427,plain,
% 11.82/1.99      ( k2_relat_1(X0) != k1_xboole_0
% 11.82/1.99      | k1_relat_1(X0) = k1_xboole_0
% 11.82/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.82/1.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_51794,plain,
% 11.82/1.99      ( k1_relat_1(sK2) = k1_xboole_0 | v1_relat_1(sK2) != iProver_top ),
% 11.82/1.99      inference(superposition,[status(thm)],[c_51768,c_51427]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_51841,plain,
% 11.82/1.99      ( k1_relat_1(sK2) = k1_xboole_0 ),
% 11.82/1.99      inference(global_propositional_subsumption,
% 11.82/1.99                [status(thm)],
% 11.82/1.99                [c_51794,c_51634]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_4,plain,
% 11.82/1.99      ( k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),X1) != k1_xboole_0
% 11.82/1.99      | k1_xboole_0 = X1 ),
% 11.82/1.99      inference(cnf_transformation,[],[f76]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_51549,plain,
% 11.82/1.99      ( k2_zfmisc_1(k1_relat_1(sK2),X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 11.82/1.99      inference(superposition,[status(thm)],[c_51520,c_4]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_51850,plain,
% 11.82/1.99      ( k2_zfmisc_1(k1_xboole_0,X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 11.82/1.99      inference(demodulation,[status(thm)],[c_51841,c_51549]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_1,plain,
% 11.82/1.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 11.82/1.99      inference(cnf_transformation,[],[f85]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_51883,plain,
% 11.82/1.99      ( k1_xboole_0 = X0 | k1_xboole_0 != k1_xboole_0 ),
% 11.82/1.99      inference(light_normalisation,[status(thm)],[c_51850,c_1]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_51884,plain,
% 11.82/1.99      ( k1_xboole_0 = X0 ),
% 11.82/1.99      inference(equality_resolution_simp,[status(thm)],[c_51883]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_19,plain,
% 11.82/1.99      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 11.82/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 11.82/1.99      | k1_xboole_0 = X1
% 11.82/1.99      | k1_xboole_0 = X0 ),
% 11.82/1.99      inference(cnf_transformation,[],[f89]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_380,plain,
% 11.82/1.99      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 11.82/1.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))
% 11.82/1.99      | sK2 != X0
% 11.82/1.99      | k1_xboole_0 = X1
% 11.82/1.99      | k1_xboole_0 = X0 ),
% 11.82/1.99      inference(resolution_lifted,[status(thm)],[c_19,c_26]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_381,plain,
% 11.82/1.99      ( ~ v1_funct_2(sK2,X0,k1_xboole_0)
% 11.82/1.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))
% 11.82/1.99      | k1_xboole_0 = X0
% 11.82/1.99      | k1_xboole_0 = sK2 ),
% 11.82/1.99      inference(unflattening,[status(thm)],[c_380]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_482,plain,
% 11.82/1.99      ( k2_enumset1(sK0,sK0,sK0,sK0) != X0
% 11.82/1.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))
% 11.82/1.99      | sK1 != k1_xboole_0
% 11.82/1.99      | sK2 != sK2
% 11.82/1.99      | sK2 = k1_xboole_0
% 11.82/1.99      | k1_xboole_0 = X0 ),
% 11.82/1.99      inference(resolution_lifted,[status(thm)],[c_27,c_381]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_483,plain,
% 11.82/1.99      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0))
% 11.82/1.99      | sK1 != k1_xboole_0
% 11.82/1.99      | sK2 = k1_xboole_0
% 11.82/1.99      | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) ),
% 11.82/1.99      inference(unflattening,[status(thm)],[c_482]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_2,plain,
% 11.82/1.99      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 11.82/1.99      | k1_xboole_0 = X1
% 11.82/1.99      | k1_xboole_0 = X0 ),
% 11.82/1.99      inference(cnf_transformation,[],[f44]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_85,plain,
% 11.82/1.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 11.82/1.99      | k1_xboole_0 = k1_xboole_0 ),
% 11.82/1.99      inference(instantiation,[status(thm)],[c_2]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_86,plain,
% 11.82/1.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 11.82/1.99      inference(instantiation,[status(thm)],[c_1]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_586,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_8057,plain,
% 11.82/1.99      ( X0 = sK1 | X0 != k1_xboole_0 | sK1 != k1_xboole_0 ),
% 11.82/1.99      inference(instantiation,[status(thm)],[c_586]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_8058,plain,
% 11.82/1.99      ( sK1 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 != k1_xboole_0 ),
% 11.82/1.99      inference(instantiation,[status(thm)],[c_8057]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_51395,plain,
% 11.82/1.99      ( sK1 != k1_xboole_0 ),
% 11.82/1.99      inference(global_propositional_subsumption,
% 11.82/1.99                [status(thm)],
% 11.82/1.99                [c_483,c_25,c_85,c_86,c_8058]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_51943,plain,
% 11.82/1.99      ( k1_xboole_0 != k1_xboole_0 ),
% 11.82/1.99      inference(demodulation,[status(thm)],[c_51884,c_51395]) ).
% 11.82/1.99  
% 11.82/1.99  cnf(c_51948,plain,
% 11.82/1.99      ( $false ),
% 11.82/1.99      inference(equality_resolution_simp,[status(thm)],[c_51943]) ).
% 11.82/1.99  
% 11.82/1.99  
% 11.82/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.82/1.99  
% 11.82/1.99  ------                               Statistics
% 11.82/1.99  
% 11.82/1.99  ------ Selected
% 11.82/1.99  
% 11.82/1.99  total_time:                             1.197
% 11.82/1.99  
%------------------------------------------------------------------------------
