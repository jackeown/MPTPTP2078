%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:58 EST 2020

% Result     : Theorem 3.38s
% Output     : CNFRefutation 3.38s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 605 expanded)
%              Number of clauses        :   63 ( 176 expanded)
%              Number of leaves         :   17 ( 138 expanded)
%              Depth                    :   19
%              Number of atoms          :  344 (1871 expanded)
%              Number of equality atoms :  181 ( 721 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f26,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f25])).

fof(f32,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
        & k1_xboole_0 != X1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1)))
      & k1_xboole_0 != sK2
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
      & v1_funct_2(sK4,k1_tarski(sK1),sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1)))
    & k1_xboole_0 != sK2
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
    & v1_funct_2(sK4,k1_tarski(sK1),sK2)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f26,f32])).

fof(f55,plain,(
    v1_funct_2(sK4,k1_tarski(sK1),sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f59,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f38,f39])).

fof(f68,plain,(
    v1_funct_2(sK4,k1_enumset1(sK1,sK1,sK1),sK2) ),
    inference(definition_unfolding,[],[f55,f59])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f56,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) ),
    inference(cnf_transformation,[],[f33])).

fof(f67,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))) ),
    inference(definition_unfolding,[],[f56,f59])).

fof(f57,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f33])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f1])).

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

fof(f35,plain,(
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
    inference(definition_unfolding,[],[f35,f59])).

fof(f69,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_enumset1(X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f62])).

fof(f70,plain,(
    ! [X3] : r2_hidden(X3,k1_enumset1(X3,X3,X3)) ),
    inference(equality_resolution,[],[f69])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f45,f59])).

fof(f54,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_enumset1(X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f41,f59])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f44,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f58,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1))) ),
    inference(cnf_transformation,[],[f33])).

fof(f66,plain,(
    ~ r1_tarski(k7_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4,sK3),k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) ),
    inference(definition_unfolding,[],[f58,f59,f59])).

cnf(c_21,negated_conjecture,
    ( v1_funct_2(sK4,k1_enumset1(sK1,sK1,sK1),sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_388,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_20])).

cnf(c_389,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | k1_relset_1(X0,X1,sK4) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_388])).

cnf(c_551,plain,
    ( k1_relset_1(X0,X1,sK4) = X0
    | k1_enumset1(sK1,sK1,sK1) != X0
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK4 != sK4
    | sK2 != X1
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_389])).

cnf(c_552,plain,
    ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4) = k1_enumset1(sK1,sK1,sK1)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_551])).

cnf(c_19,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_553,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))
    | k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4) = k1_enumset1(sK1,sK1,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_552,c_19])).

cnf(c_554,plain,
    ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4) = k1_enumset1(sK1,sK1,sK1)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
    inference(renaming,[status(thm)],[c_553])).

cnf(c_614,plain,
    ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4) = k1_enumset1(sK1,sK1,sK1) ),
    inference(equality_resolution_simp,[status(thm)],[c_554])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_433,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_20])).

cnf(c_434,plain,
    ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_433])).

cnf(c_1098,plain,
    ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4) = k1_relat_1(sK4) ),
    inference(equality_resolution,[status(thm)],[c_434])).

cnf(c_1272,plain,
    ( k1_enumset1(sK1,sK1,sK1) = k1_relat_1(sK4) ),
    inference(light_normalisation,[status(thm)],[c_614,c_1098])).

cnf(c_2,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1006,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1387,plain,
    ( r2_hidden(sK1,k1_relat_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1272,c_1006])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_272,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_22])).

cnf(c_273,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_272])).

cnf(c_999,plain,
    ( k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0)
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_273])).

cnf(c_274,plain,
    ( k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0)
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_273])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_373,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_20])).

cnf(c_374,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_373])).

cnf(c_1049,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_374])).

cnf(c_1117,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))
    | v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_1049])).

cnf(c_1118,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))
    | v1_relat_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1117])).

cnf(c_780,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1164,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) = k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_780])).

cnf(c_6,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1182,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1183,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1182])).

cnf(c_1888,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_999,c_274,c_1118,c_1164,c_1183])).

cnf(c_1889,plain,
    ( k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0)
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1888])).

cnf(c_2057,plain,
    ( k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) = k11_relat_1(sK4,sK1) ),
    inference(superposition,[status(thm)],[c_1387,c_1889])).

cnf(c_998,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_374])).

cnf(c_1315,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_998,c_1118,c_1164,c_1183])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_enumset1(X1,X1,X1)) = k11_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1004,plain,
    ( k9_relat_1(X0,k1_enumset1(X1,X1,X1)) = k11_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2018,plain,
    ( k9_relat_1(sK4,k1_enumset1(X0,X0,X0)) = k11_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_1315,c_1004])).

cnf(c_2104,plain,
    ( k9_relat_1(sK4,k1_relat_1(sK4)) = k11_relat_1(sK4,sK1) ),
    inference(superposition,[status(thm)],[c_1272,c_2018])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1001,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1391,plain,
    ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1315,c_1001])).

cnf(c_2106,plain,
    ( k11_relat_1(sK4,sK1) = k2_relat_1(sK4) ),
    inference(light_normalisation,[status(thm)],[c_2104,c_1391])).

cnf(c_2110,plain,
    ( k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) = k2_relat_1(sK4) ),
    inference(light_normalisation,[status(thm)],[c_2057,c_2057,c_2106])).

cnf(c_7,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1382,plain,
    ( r1_tarski(k9_relat_1(sK4,sK3),k2_relat_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_789,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1023,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k7_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4,sK3),k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)))
    | k7_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4,sK3) != X0
    | k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) != X1 ),
    inference(instantiation,[status(thm)],[c_789])).

cnf(c_1152,plain,
    ( r1_tarski(k7_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4,sK3),k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)))
    | ~ r1_tarski(k9_relat_1(sK4,sK3),X0)
    | k7_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4,sK3) != k9_relat_1(sK4,sK3)
    | k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) != X0 ),
    inference(instantiation,[status(thm)],[c_1023])).

cnf(c_1302,plain,
    ( r1_tarski(k7_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4,sK3),k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)))
    | ~ r1_tarski(k9_relat_1(sK4,sK3),k2_relat_1(sK4))
    | k7_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4,sK3) != k9_relat_1(sK4,sK3)
    | k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) != k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1152])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_424,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_20])).

cnf(c_425,plain,
    ( k7_relset_1(X0,X1,sK4,X2) = k9_relat_1(sK4,X2)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_424])).

cnf(c_1101,plain,
    ( k7_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4,X0) = k9_relat_1(sK4,X0)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_425])).

cnf(c_1151,plain,
    ( k7_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4,sK3) = k9_relat_1(sK4,sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_1101])).

cnf(c_18,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4,sK3),k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) ),
    inference(cnf_transformation,[],[f66])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2110,c_1382,c_1302,c_1182,c_1164,c_1151,c_1117,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:50:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.38/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/0.99  
% 3.38/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.38/0.99  
% 3.38/0.99  ------  iProver source info
% 3.38/0.99  
% 3.38/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.38/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.38/0.99  git: non_committed_changes: false
% 3.38/0.99  git: last_make_outside_of_git: false
% 3.38/0.99  
% 3.38/0.99  ------ 
% 3.38/0.99  
% 3.38/0.99  ------ Input Options
% 3.38/0.99  
% 3.38/0.99  --out_options                           all
% 3.38/0.99  --tptp_safe_out                         true
% 3.38/0.99  --problem_path                          ""
% 3.38/0.99  --include_path                          ""
% 3.38/0.99  --clausifier                            res/vclausify_rel
% 3.38/0.99  --clausifier_options                    ""
% 3.38/0.99  --stdin                                 false
% 3.38/0.99  --stats_out                             all
% 3.38/0.99  
% 3.38/0.99  ------ General Options
% 3.38/0.99  
% 3.38/0.99  --fof                                   false
% 3.38/0.99  --time_out_real                         305.
% 3.38/0.99  --time_out_virtual                      -1.
% 3.38/0.99  --symbol_type_check                     false
% 3.38/0.99  --clausify_out                          false
% 3.38/0.99  --sig_cnt_out                           false
% 3.38/0.99  --trig_cnt_out                          false
% 3.38/0.99  --trig_cnt_out_tolerance                1.
% 3.38/0.99  --trig_cnt_out_sk_spl                   false
% 3.38/0.99  --abstr_cl_out                          false
% 3.38/0.99  
% 3.38/0.99  ------ Global Options
% 3.38/0.99  
% 3.38/0.99  --schedule                              default
% 3.38/0.99  --add_important_lit                     false
% 3.38/0.99  --prop_solver_per_cl                    1000
% 3.38/0.99  --min_unsat_core                        false
% 3.38/0.99  --soft_assumptions                      false
% 3.38/0.99  --soft_lemma_size                       3
% 3.38/0.99  --prop_impl_unit_size                   0
% 3.38/0.99  --prop_impl_unit                        []
% 3.38/0.99  --share_sel_clauses                     true
% 3.38/0.99  --reset_solvers                         false
% 3.38/0.99  --bc_imp_inh                            [conj_cone]
% 3.38/0.99  --conj_cone_tolerance                   3.
% 3.38/0.99  --extra_neg_conj                        none
% 3.38/0.99  --large_theory_mode                     true
% 3.38/0.99  --prolific_symb_bound                   200
% 3.38/0.99  --lt_threshold                          2000
% 3.38/0.99  --clause_weak_htbl                      true
% 3.38/0.99  --gc_record_bc_elim                     false
% 3.38/0.99  
% 3.38/0.99  ------ Preprocessing Options
% 3.38/0.99  
% 3.38/0.99  --preprocessing_flag                    true
% 3.38/0.99  --time_out_prep_mult                    0.1
% 3.38/0.99  --splitting_mode                        input
% 3.38/0.99  --splitting_grd                         true
% 3.38/0.99  --splitting_cvd                         false
% 3.38/0.99  --splitting_cvd_svl                     false
% 3.38/0.99  --splitting_nvd                         32
% 3.38/0.99  --sub_typing                            true
% 3.38/0.99  --prep_gs_sim                           true
% 3.38/0.99  --prep_unflatten                        true
% 3.38/0.99  --prep_res_sim                          true
% 3.38/0.99  --prep_upred                            true
% 3.38/0.99  --prep_sem_filter                       exhaustive
% 3.38/0.99  --prep_sem_filter_out                   false
% 3.38/0.99  --pred_elim                             true
% 3.38/0.99  --res_sim_input                         true
% 3.38/0.99  --eq_ax_congr_red                       true
% 3.38/0.99  --pure_diseq_elim                       true
% 3.38/0.99  --brand_transform                       false
% 3.38/0.99  --non_eq_to_eq                          false
% 3.38/0.99  --prep_def_merge                        true
% 3.38/0.99  --prep_def_merge_prop_impl              false
% 3.38/0.99  --prep_def_merge_mbd                    true
% 3.38/0.99  --prep_def_merge_tr_red                 false
% 3.38/0.99  --prep_def_merge_tr_cl                  false
% 3.38/0.99  --smt_preprocessing                     true
% 3.38/0.99  --smt_ac_axioms                         fast
% 3.38/0.99  --preprocessed_out                      false
% 3.38/0.99  --preprocessed_stats                    false
% 3.38/0.99  
% 3.38/0.99  ------ Abstraction refinement Options
% 3.38/0.99  
% 3.38/0.99  --abstr_ref                             []
% 3.38/0.99  --abstr_ref_prep                        false
% 3.38/0.99  --abstr_ref_until_sat                   false
% 3.38/0.99  --abstr_ref_sig_restrict                funpre
% 3.38/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.38/0.99  --abstr_ref_under                       []
% 3.38/0.99  
% 3.38/0.99  ------ SAT Options
% 3.38/0.99  
% 3.38/0.99  --sat_mode                              false
% 3.38/0.99  --sat_fm_restart_options                ""
% 3.38/0.99  --sat_gr_def                            false
% 3.38/0.99  --sat_epr_types                         true
% 3.38/0.99  --sat_non_cyclic_types                  false
% 3.38/0.99  --sat_finite_models                     false
% 3.38/0.99  --sat_fm_lemmas                         false
% 3.38/0.99  --sat_fm_prep                           false
% 3.38/0.99  --sat_fm_uc_incr                        true
% 3.38/0.99  --sat_out_model                         small
% 3.38/0.99  --sat_out_clauses                       false
% 3.38/0.99  
% 3.38/0.99  ------ QBF Options
% 3.38/0.99  
% 3.38/0.99  --qbf_mode                              false
% 3.38/0.99  --qbf_elim_univ                         false
% 3.38/0.99  --qbf_dom_inst                          none
% 3.38/0.99  --qbf_dom_pre_inst                      false
% 3.38/0.99  --qbf_sk_in                             false
% 3.38/0.99  --qbf_pred_elim                         true
% 3.38/0.99  --qbf_split                             512
% 3.38/0.99  
% 3.38/0.99  ------ BMC1 Options
% 3.38/0.99  
% 3.38/0.99  --bmc1_incremental                      false
% 3.38/0.99  --bmc1_axioms                           reachable_all
% 3.38/0.99  --bmc1_min_bound                        0
% 3.38/0.99  --bmc1_max_bound                        -1
% 3.38/0.99  --bmc1_max_bound_default                -1
% 3.38/0.99  --bmc1_symbol_reachability              true
% 3.38/0.99  --bmc1_property_lemmas                  false
% 3.38/0.99  --bmc1_k_induction                      false
% 3.38/0.99  --bmc1_non_equiv_states                 false
% 3.38/0.99  --bmc1_deadlock                         false
% 3.38/0.99  --bmc1_ucm                              false
% 3.38/0.99  --bmc1_add_unsat_core                   none
% 3.38/0.99  --bmc1_unsat_core_children              false
% 3.38/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.38/0.99  --bmc1_out_stat                         full
% 3.38/0.99  --bmc1_ground_init                      false
% 3.38/0.99  --bmc1_pre_inst_next_state              false
% 3.38/0.99  --bmc1_pre_inst_state                   false
% 3.38/0.99  --bmc1_pre_inst_reach_state             false
% 3.38/0.99  --bmc1_out_unsat_core                   false
% 3.38/0.99  --bmc1_aig_witness_out                  false
% 3.38/0.99  --bmc1_verbose                          false
% 3.38/0.99  --bmc1_dump_clauses_tptp                false
% 3.38/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.38/0.99  --bmc1_dump_file                        -
% 3.38/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.38/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.38/0.99  --bmc1_ucm_extend_mode                  1
% 3.38/0.99  --bmc1_ucm_init_mode                    2
% 3.38/0.99  --bmc1_ucm_cone_mode                    none
% 3.38/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.38/0.99  --bmc1_ucm_relax_model                  4
% 3.38/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.38/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.38/0.99  --bmc1_ucm_layered_model                none
% 3.38/0.99  --bmc1_ucm_max_lemma_size               10
% 3.38/0.99  
% 3.38/0.99  ------ AIG Options
% 3.38/0.99  
% 3.38/0.99  --aig_mode                              false
% 3.38/0.99  
% 3.38/0.99  ------ Instantiation Options
% 3.38/0.99  
% 3.38/0.99  --instantiation_flag                    true
% 3.38/0.99  --inst_sos_flag                         true
% 3.38/0.99  --inst_sos_phase                        true
% 3.38/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.38/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.38/0.99  --inst_lit_sel_side                     num_symb
% 3.38/0.99  --inst_solver_per_active                1400
% 3.38/0.99  --inst_solver_calls_frac                1.
% 3.38/0.99  --inst_passive_queue_type               priority_queues
% 3.38/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.38/0.99  --inst_passive_queues_freq              [25;2]
% 3.38/0.99  --inst_dismatching                      true
% 3.38/0.99  --inst_eager_unprocessed_to_passive     true
% 3.38/0.99  --inst_prop_sim_given                   true
% 3.38/0.99  --inst_prop_sim_new                     false
% 3.38/0.99  --inst_subs_new                         false
% 3.38/0.99  --inst_eq_res_simp                      false
% 3.38/0.99  --inst_subs_given                       false
% 3.38/0.99  --inst_orphan_elimination               true
% 3.38/0.99  --inst_learning_loop_flag               true
% 3.38/0.99  --inst_learning_start                   3000
% 3.38/0.99  --inst_learning_factor                  2
% 3.38/0.99  --inst_start_prop_sim_after_learn       3
% 3.38/0.99  --inst_sel_renew                        solver
% 3.38/0.99  --inst_lit_activity_flag                true
% 3.38/0.99  --inst_restr_to_given                   false
% 3.38/0.99  --inst_activity_threshold               500
% 3.38/0.99  --inst_out_proof                        true
% 3.38/0.99  
% 3.38/0.99  ------ Resolution Options
% 3.38/0.99  
% 3.38/0.99  --resolution_flag                       true
% 3.38/0.99  --res_lit_sel                           adaptive
% 3.38/0.99  --res_lit_sel_side                      none
% 3.38/0.99  --res_ordering                          kbo
% 3.38/0.99  --res_to_prop_solver                    active
% 3.38/0.99  --res_prop_simpl_new                    false
% 3.38/0.99  --res_prop_simpl_given                  true
% 3.38/0.99  --res_passive_queue_type                priority_queues
% 3.38/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.38/0.99  --res_passive_queues_freq               [15;5]
% 3.38/0.99  --res_forward_subs                      full
% 3.38/0.99  --res_backward_subs                     full
% 3.38/0.99  --res_forward_subs_resolution           true
% 3.38/0.99  --res_backward_subs_resolution          true
% 3.38/0.99  --res_orphan_elimination                true
% 3.38/0.99  --res_time_limit                        2.
% 3.38/0.99  --res_out_proof                         true
% 3.38/0.99  
% 3.38/0.99  ------ Superposition Options
% 3.38/0.99  
% 3.38/0.99  --superposition_flag                    true
% 3.38/0.99  --sup_passive_queue_type                priority_queues
% 3.38/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.38/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.38/0.99  --demod_completeness_check              fast
% 3.38/0.99  --demod_use_ground                      true
% 3.38/0.99  --sup_to_prop_solver                    passive
% 3.38/0.99  --sup_prop_simpl_new                    true
% 3.38/0.99  --sup_prop_simpl_given                  true
% 3.38/0.99  --sup_fun_splitting                     true
% 3.38/0.99  --sup_smt_interval                      50000
% 3.38/0.99  
% 3.38/0.99  ------ Superposition Simplification Setup
% 3.38/0.99  
% 3.38/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.38/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.38/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.38/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.38/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.38/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.38/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.38/0.99  --sup_immed_triv                        [TrivRules]
% 3.38/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.38/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.38/0.99  --sup_immed_bw_main                     []
% 3.38/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.38/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.38/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.38/0.99  --sup_input_bw                          []
% 3.38/0.99  
% 3.38/0.99  ------ Combination Options
% 3.38/0.99  
% 3.38/0.99  --comb_res_mult                         3
% 3.38/0.99  --comb_sup_mult                         2
% 3.38/0.99  --comb_inst_mult                        10
% 3.38/0.99  
% 3.38/0.99  ------ Debug Options
% 3.38/0.99  
% 3.38/0.99  --dbg_backtrace                         false
% 3.38/0.99  --dbg_dump_prop_clauses                 false
% 3.38/0.99  --dbg_dump_prop_clauses_file            -
% 3.38/0.99  --dbg_out_stat                          false
% 3.38/0.99  ------ Parsing...
% 3.38/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.38/0.99  
% 3.38/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.38/0.99  
% 3.38/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.38/0.99  
% 3.38/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.38/0.99  ------ Proving...
% 3.38/0.99  ------ Problem Properties 
% 3.38/0.99  
% 3.38/0.99  
% 3.38/0.99  clauses                                 17
% 3.38/0.99  conjectures                             2
% 3.38/0.99  EPR                                     1
% 3.38/0.99  Horn                                    15
% 3.38/0.99  unary                                   5
% 3.38/0.99  binary                                  6
% 3.38/0.99  lits                                    36
% 3.38/0.99  lits eq                                 22
% 3.38/0.99  fd_pure                                 0
% 3.38/0.99  fd_pseudo                               0
% 3.38/0.99  fd_cond                                 0
% 3.38/0.99  fd_pseudo_cond                          2
% 3.38/0.99  AC symbols                              0
% 3.38/0.99  
% 3.38/0.99  ------ Schedule dynamic 5 is on 
% 3.38/0.99  
% 3.38/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.38/0.99  
% 3.38/0.99  
% 3.38/0.99  ------ 
% 3.38/0.99  Current options:
% 3.38/0.99  ------ 
% 3.38/0.99  
% 3.38/0.99  ------ Input Options
% 3.38/0.99  
% 3.38/0.99  --out_options                           all
% 3.38/0.99  --tptp_safe_out                         true
% 3.38/0.99  --problem_path                          ""
% 3.38/0.99  --include_path                          ""
% 3.38/0.99  --clausifier                            res/vclausify_rel
% 3.38/0.99  --clausifier_options                    ""
% 3.38/0.99  --stdin                                 false
% 3.38/0.99  --stats_out                             all
% 3.38/0.99  
% 3.38/0.99  ------ General Options
% 3.38/0.99  
% 3.38/0.99  --fof                                   false
% 3.38/0.99  --time_out_real                         305.
% 3.38/0.99  --time_out_virtual                      -1.
% 3.38/0.99  --symbol_type_check                     false
% 3.38/0.99  --clausify_out                          false
% 3.38/0.99  --sig_cnt_out                           false
% 3.38/0.99  --trig_cnt_out                          false
% 3.38/0.99  --trig_cnt_out_tolerance                1.
% 3.38/0.99  --trig_cnt_out_sk_spl                   false
% 3.38/0.99  --abstr_cl_out                          false
% 3.38/0.99  
% 3.38/0.99  ------ Global Options
% 3.38/0.99  
% 3.38/0.99  --schedule                              default
% 3.38/0.99  --add_important_lit                     false
% 3.38/0.99  --prop_solver_per_cl                    1000
% 3.38/0.99  --min_unsat_core                        false
% 3.38/0.99  --soft_assumptions                      false
% 3.38/0.99  --soft_lemma_size                       3
% 3.38/0.99  --prop_impl_unit_size                   0
% 3.38/0.99  --prop_impl_unit                        []
% 3.38/0.99  --share_sel_clauses                     true
% 3.38/0.99  --reset_solvers                         false
% 3.38/0.99  --bc_imp_inh                            [conj_cone]
% 3.38/0.99  --conj_cone_tolerance                   3.
% 3.38/0.99  --extra_neg_conj                        none
% 3.38/0.99  --large_theory_mode                     true
% 3.38/0.99  --prolific_symb_bound                   200
% 3.38/0.99  --lt_threshold                          2000
% 3.38/0.99  --clause_weak_htbl                      true
% 3.38/0.99  --gc_record_bc_elim                     false
% 3.38/0.99  
% 3.38/0.99  ------ Preprocessing Options
% 3.38/0.99  
% 3.38/0.99  --preprocessing_flag                    true
% 3.38/0.99  --time_out_prep_mult                    0.1
% 3.38/0.99  --splitting_mode                        input
% 3.38/0.99  --splitting_grd                         true
% 3.38/0.99  --splitting_cvd                         false
% 3.38/0.99  --splitting_cvd_svl                     false
% 3.38/0.99  --splitting_nvd                         32
% 3.38/0.99  --sub_typing                            true
% 3.38/0.99  --prep_gs_sim                           true
% 3.38/0.99  --prep_unflatten                        true
% 3.38/0.99  --prep_res_sim                          true
% 3.38/0.99  --prep_upred                            true
% 3.38/0.99  --prep_sem_filter                       exhaustive
% 3.38/0.99  --prep_sem_filter_out                   false
% 3.38/0.99  --pred_elim                             true
% 3.38/0.99  --res_sim_input                         true
% 3.38/0.99  --eq_ax_congr_red                       true
% 3.38/0.99  --pure_diseq_elim                       true
% 3.38/0.99  --brand_transform                       false
% 3.38/0.99  --non_eq_to_eq                          false
% 3.38/0.99  --prep_def_merge                        true
% 3.38/0.99  --prep_def_merge_prop_impl              false
% 3.38/0.99  --prep_def_merge_mbd                    true
% 3.38/0.99  --prep_def_merge_tr_red                 false
% 3.38/0.99  --prep_def_merge_tr_cl                  false
% 3.38/0.99  --smt_preprocessing                     true
% 3.38/0.99  --smt_ac_axioms                         fast
% 3.38/0.99  --preprocessed_out                      false
% 3.38/0.99  --preprocessed_stats                    false
% 3.38/0.99  
% 3.38/0.99  ------ Abstraction refinement Options
% 3.38/0.99  
% 3.38/0.99  --abstr_ref                             []
% 3.38/0.99  --abstr_ref_prep                        false
% 3.38/0.99  --abstr_ref_until_sat                   false
% 3.38/0.99  --abstr_ref_sig_restrict                funpre
% 3.38/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.38/0.99  --abstr_ref_under                       []
% 3.38/0.99  
% 3.38/0.99  ------ SAT Options
% 3.38/0.99  
% 3.38/0.99  --sat_mode                              false
% 3.38/0.99  --sat_fm_restart_options                ""
% 3.38/0.99  --sat_gr_def                            false
% 3.38/0.99  --sat_epr_types                         true
% 3.38/0.99  --sat_non_cyclic_types                  false
% 3.38/0.99  --sat_finite_models                     false
% 3.38/0.99  --sat_fm_lemmas                         false
% 3.38/0.99  --sat_fm_prep                           false
% 3.38/0.99  --sat_fm_uc_incr                        true
% 3.38/0.99  --sat_out_model                         small
% 3.38/0.99  --sat_out_clauses                       false
% 3.38/0.99  
% 3.38/0.99  ------ QBF Options
% 3.38/0.99  
% 3.38/0.99  --qbf_mode                              false
% 3.38/0.99  --qbf_elim_univ                         false
% 3.38/0.99  --qbf_dom_inst                          none
% 3.38/0.99  --qbf_dom_pre_inst                      false
% 3.38/0.99  --qbf_sk_in                             false
% 3.38/0.99  --qbf_pred_elim                         true
% 3.38/0.99  --qbf_split                             512
% 3.38/0.99  
% 3.38/0.99  ------ BMC1 Options
% 3.38/0.99  
% 3.38/0.99  --bmc1_incremental                      false
% 3.38/0.99  --bmc1_axioms                           reachable_all
% 3.38/0.99  --bmc1_min_bound                        0
% 3.38/0.99  --bmc1_max_bound                        -1
% 3.38/0.99  --bmc1_max_bound_default                -1
% 3.38/0.99  --bmc1_symbol_reachability              true
% 3.38/0.99  --bmc1_property_lemmas                  false
% 3.38/0.99  --bmc1_k_induction                      false
% 3.38/0.99  --bmc1_non_equiv_states                 false
% 3.38/0.99  --bmc1_deadlock                         false
% 3.38/0.99  --bmc1_ucm                              false
% 3.38/0.99  --bmc1_add_unsat_core                   none
% 3.38/0.99  --bmc1_unsat_core_children              false
% 3.38/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.38/0.99  --bmc1_out_stat                         full
% 3.38/0.99  --bmc1_ground_init                      false
% 3.38/0.99  --bmc1_pre_inst_next_state              false
% 3.38/0.99  --bmc1_pre_inst_state                   false
% 3.38/0.99  --bmc1_pre_inst_reach_state             false
% 3.38/0.99  --bmc1_out_unsat_core                   false
% 3.38/0.99  --bmc1_aig_witness_out                  false
% 3.38/0.99  --bmc1_verbose                          false
% 3.38/0.99  --bmc1_dump_clauses_tptp                false
% 3.38/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.38/0.99  --bmc1_dump_file                        -
% 3.38/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.38/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.38/0.99  --bmc1_ucm_extend_mode                  1
% 3.38/0.99  --bmc1_ucm_init_mode                    2
% 3.38/0.99  --bmc1_ucm_cone_mode                    none
% 3.38/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.38/0.99  --bmc1_ucm_relax_model                  4
% 3.38/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.38/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.38/0.99  --bmc1_ucm_layered_model                none
% 3.38/0.99  --bmc1_ucm_max_lemma_size               10
% 3.38/0.99  
% 3.38/0.99  ------ AIG Options
% 3.38/0.99  
% 3.38/0.99  --aig_mode                              false
% 3.38/0.99  
% 3.38/0.99  ------ Instantiation Options
% 3.38/0.99  
% 3.38/0.99  --instantiation_flag                    true
% 3.38/0.99  --inst_sos_flag                         true
% 3.38/0.99  --inst_sos_phase                        true
% 3.38/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.38/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.38/0.99  --inst_lit_sel_side                     none
% 3.38/0.99  --inst_solver_per_active                1400
% 3.38/0.99  --inst_solver_calls_frac                1.
% 3.38/0.99  --inst_passive_queue_type               priority_queues
% 3.38/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.38/0.99  --inst_passive_queues_freq              [25;2]
% 3.38/0.99  --inst_dismatching                      true
% 3.38/0.99  --inst_eager_unprocessed_to_passive     true
% 3.38/0.99  --inst_prop_sim_given                   true
% 3.38/0.99  --inst_prop_sim_new                     false
% 3.38/0.99  --inst_subs_new                         false
% 3.38/0.99  --inst_eq_res_simp                      false
% 3.38/0.99  --inst_subs_given                       false
% 3.38/0.99  --inst_orphan_elimination               true
% 3.38/0.99  --inst_learning_loop_flag               true
% 3.38/0.99  --inst_learning_start                   3000
% 3.38/0.99  --inst_learning_factor                  2
% 3.38/0.99  --inst_start_prop_sim_after_learn       3
% 3.38/0.99  --inst_sel_renew                        solver
% 3.38/0.99  --inst_lit_activity_flag                true
% 3.38/0.99  --inst_restr_to_given                   false
% 3.38/0.99  --inst_activity_threshold               500
% 3.38/0.99  --inst_out_proof                        true
% 3.38/0.99  
% 3.38/0.99  ------ Resolution Options
% 3.38/0.99  
% 3.38/0.99  --resolution_flag                       false
% 3.38/0.99  --res_lit_sel                           adaptive
% 3.38/0.99  --res_lit_sel_side                      none
% 3.38/0.99  --res_ordering                          kbo
% 3.38/0.99  --res_to_prop_solver                    active
% 3.38/0.99  --res_prop_simpl_new                    false
% 3.38/0.99  --res_prop_simpl_given                  true
% 3.38/0.99  --res_passive_queue_type                priority_queues
% 3.38/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.38/0.99  --res_passive_queues_freq               [15;5]
% 3.38/0.99  --res_forward_subs                      full
% 3.38/0.99  --res_backward_subs                     full
% 3.38/0.99  --res_forward_subs_resolution           true
% 3.38/0.99  --res_backward_subs_resolution          true
% 3.38/0.99  --res_orphan_elimination                true
% 3.38/0.99  --res_time_limit                        2.
% 3.38/0.99  --res_out_proof                         true
% 3.38/0.99  
% 3.38/0.99  ------ Superposition Options
% 3.38/0.99  
% 3.38/0.99  --superposition_flag                    true
% 3.38/0.99  --sup_passive_queue_type                priority_queues
% 3.38/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.38/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.38/0.99  --demod_completeness_check              fast
% 3.38/0.99  --demod_use_ground                      true
% 3.38/0.99  --sup_to_prop_solver                    passive
% 3.38/0.99  --sup_prop_simpl_new                    true
% 3.38/0.99  --sup_prop_simpl_given                  true
% 3.38/0.99  --sup_fun_splitting                     true
% 3.38/0.99  --sup_smt_interval                      50000
% 3.38/0.99  
% 3.38/0.99  ------ Superposition Simplification Setup
% 3.38/0.99  
% 3.38/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.38/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.38/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.38/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.38/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.38/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.38/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.38/0.99  --sup_immed_triv                        [TrivRules]
% 3.38/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.38/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.38/0.99  --sup_immed_bw_main                     []
% 3.38/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.38/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.38/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.38/0.99  --sup_input_bw                          []
% 3.38/0.99  
% 3.38/0.99  ------ Combination Options
% 3.38/0.99  
% 3.38/0.99  --comb_res_mult                         3
% 3.38/0.99  --comb_sup_mult                         2
% 3.38/0.99  --comb_inst_mult                        10
% 3.38/0.99  
% 3.38/0.99  ------ Debug Options
% 3.38/0.99  
% 3.38/0.99  --dbg_backtrace                         false
% 3.38/0.99  --dbg_dump_prop_clauses                 false
% 3.38/0.99  --dbg_dump_prop_clauses_file            -
% 3.38/0.99  --dbg_out_stat                          false
% 3.38/0.99  
% 3.38/0.99  
% 3.38/0.99  
% 3.38/0.99  
% 3.38/0.99  ------ Proving...
% 3.38/0.99  
% 3.38/0.99  
% 3.38/0.99  % SZS status Theorem for theBenchmark.p
% 3.38/0.99  
% 3.38/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.38/0.99  
% 3.38/0.99  fof(f13,conjecture,(
% 3.38/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 3.38/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/0.99  
% 3.38/0.99  fof(f14,negated_conjecture,(
% 3.38/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 3.38/0.99    inference(negated_conjecture,[],[f13])).
% 3.38/0.99  
% 3.38/0.99  fof(f25,plain,(
% 3.38/0.99    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)))),
% 3.38/0.99    inference(ennf_transformation,[],[f14])).
% 3.38/0.99  
% 3.38/0.99  fof(f26,plain,(
% 3.38/0.99    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3))),
% 3.38/0.99    inference(flattening,[],[f25])).
% 3.38/0.99  
% 3.38/0.99  fof(f32,plain,(
% 3.38/0.99    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1))) & k1_xboole_0 != sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK4,k1_tarski(sK1),sK2) & v1_funct_1(sK4))),
% 3.38/0.99    introduced(choice_axiom,[])).
% 3.38/0.99  
% 3.38/0.99  fof(f33,plain,(
% 3.38/0.99    ~r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1))) & k1_xboole_0 != sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK4,k1_tarski(sK1),sK2) & v1_funct_1(sK4)),
% 3.38/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f26,f32])).
% 3.38/0.99  
% 3.38/0.99  fof(f55,plain,(
% 3.38/0.99    v1_funct_2(sK4,k1_tarski(sK1),sK2)),
% 3.38/0.99    inference(cnf_transformation,[],[f33])).
% 3.38/0.99  
% 3.38/0.99  fof(f2,axiom,(
% 3.38/0.99    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.38/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/0.99  
% 3.38/0.99  fof(f38,plain,(
% 3.38/0.99    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.38/0.99    inference(cnf_transformation,[],[f2])).
% 3.38/0.99  
% 3.38/0.99  fof(f3,axiom,(
% 3.38/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.38/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/0.99  
% 3.38/0.99  fof(f39,plain,(
% 3.38/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.38/0.99    inference(cnf_transformation,[],[f3])).
% 3.38/0.99  
% 3.38/0.99  fof(f59,plain,(
% 3.38/0.99    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 3.38/0.99    inference(definition_unfolding,[],[f38,f39])).
% 3.38/0.99  
% 3.38/0.99  fof(f68,plain,(
% 3.38/0.99    v1_funct_2(sK4,k1_enumset1(sK1,sK1,sK1),sK2)),
% 3.38/0.99    inference(definition_unfolding,[],[f55,f59])).
% 3.38/0.99  
% 3.38/0.99  fof(f12,axiom,(
% 3.38/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.38/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/0.99  
% 3.38/0.99  fof(f23,plain,(
% 3.38/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.38/0.99    inference(ennf_transformation,[],[f12])).
% 3.38/0.99  
% 3.38/0.99  fof(f24,plain,(
% 3.38/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.38/0.99    inference(flattening,[],[f23])).
% 3.38/0.99  
% 3.38/0.99  fof(f31,plain,(
% 3.38/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.38/0.99    inference(nnf_transformation,[],[f24])).
% 3.38/0.99  
% 3.38/0.99  fof(f48,plain,(
% 3.38/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.38/0.99    inference(cnf_transformation,[],[f31])).
% 3.38/0.99  
% 3.38/0.99  fof(f56,plain,(
% 3.38/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))),
% 3.38/0.99    inference(cnf_transformation,[],[f33])).
% 3.38/0.99  
% 3.38/0.99  fof(f67,plain,(
% 3.38/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)))),
% 3.38/0.99    inference(definition_unfolding,[],[f56,f59])).
% 3.38/0.99  
% 3.38/0.99  fof(f57,plain,(
% 3.38/0.99    k1_xboole_0 != sK2),
% 3.38/0.99    inference(cnf_transformation,[],[f33])).
% 3.38/0.99  
% 3.38/0.99  fof(f10,axiom,(
% 3.38/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.38/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/0.99  
% 3.38/0.99  fof(f21,plain,(
% 3.38/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.38/0.99    inference(ennf_transformation,[],[f10])).
% 3.38/0.99  
% 3.38/0.99  fof(f46,plain,(
% 3.38/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.38/0.99    inference(cnf_transformation,[],[f21])).
% 3.38/0.99  
% 3.38/0.99  fof(f1,axiom,(
% 3.38/0.99    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.38/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/0.99  
% 3.38/0.99  fof(f27,plain,(
% 3.38/0.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.38/0.99    inference(nnf_transformation,[],[f1])).
% 3.38/0.99  
% 3.38/0.99  fof(f28,plain,(
% 3.38/0.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.38/0.99    inference(rectify,[],[f27])).
% 3.38/0.99  
% 3.38/0.99  fof(f29,plain,(
% 3.38/0.99    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1))))),
% 3.38/0.99    introduced(choice_axiom,[])).
% 3.38/0.99  
% 3.38/0.99  fof(f30,plain,(
% 3.38/0.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.38/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 3.38/0.99  
% 3.38/0.99  fof(f35,plain,(
% 3.38/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 3.38/0.99    inference(cnf_transformation,[],[f30])).
% 3.38/0.99  
% 3.38/0.99  fof(f62,plain,(
% 3.38/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_enumset1(X0,X0,X0) != X1) )),
% 3.38/0.99    inference(definition_unfolding,[],[f35,f59])).
% 3.38/0.99  
% 3.38/0.99  fof(f69,plain,(
% 3.38/0.99    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_enumset1(X3,X3,X3) != X1) )),
% 3.38/0.99    inference(equality_resolution,[],[f62])).
% 3.38/0.99  
% 3.38/0.99  fof(f70,plain,(
% 3.38/0.99    ( ! [X3] : (r2_hidden(X3,k1_enumset1(X3,X3,X3))) )),
% 3.38/0.99    inference(equality_resolution,[],[f69])).
% 3.38/0.99  
% 3.38/0.99  fof(f9,axiom,(
% 3.38/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)))),
% 3.38/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/0.99  
% 3.38/0.99  fof(f19,plain,(
% 3.38/0.99    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.38/0.99    inference(ennf_transformation,[],[f9])).
% 3.38/0.99  
% 3.38/0.99  fof(f20,plain,(
% 3.38/0.99    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.38/0.99    inference(flattening,[],[f19])).
% 3.38/0.99  
% 3.38/0.99  fof(f45,plain,(
% 3.38/0.99    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.38/0.99    inference(cnf_transformation,[],[f20])).
% 3.38/0.99  
% 3.38/0.99  fof(f65,plain,(
% 3.38/0.99    ( ! [X0,X1] : (k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.38/0.99    inference(definition_unfolding,[],[f45,f59])).
% 3.38/0.99  
% 3.38/0.99  fof(f54,plain,(
% 3.38/0.99    v1_funct_1(sK4)),
% 3.38/0.99    inference(cnf_transformation,[],[f33])).
% 3.38/0.99  
% 3.38/0.99  fof(f4,axiom,(
% 3.38/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.38/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/0.99  
% 3.38/0.99  fof(f15,plain,(
% 3.38/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.38/0.99    inference(ennf_transformation,[],[f4])).
% 3.38/0.99  
% 3.38/0.99  fof(f40,plain,(
% 3.38/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.38/0.99    inference(cnf_transformation,[],[f15])).
% 3.38/0.99  
% 3.38/0.99  fof(f6,axiom,(
% 3.38/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.38/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/0.99  
% 3.38/0.99  fof(f42,plain,(
% 3.38/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.38/0.99    inference(cnf_transformation,[],[f6])).
% 3.38/0.99  
% 3.38/0.99  fof(f5,axiom,(
% 3.38/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 3.38/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/0.99  
% 3.38/0.99  fof(f16,plain,(
% 3.38/0.99    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 3.38/0.99    inference(ennf_transformation,[],[f5])).
% 3.38/0.99  
% 3.38/0.99  fof(f41,plain,(
% 3.38/0.99    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 3.38/0.99    inference(cnf_transformation,[],[f16])).
% 3.38/0.99  
% 3.38/0.99  fof(f64,plain,(
% 3.38/0.99    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_enumset1(X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 3.38/0.99    inference(definition_unfolding,[],[f41,f59])).
% 3.38/0.99  
% 3.38/0.99  fof(f8,axiom,(
% 3.38/0.99    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 3.38/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/0.99  
% 3.38/0.99  fof(f18,plain,(
% 3.38/0.99    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 3.38/0.99    inference(ennf_transformation,[],[f8])).
% 3.38/0.99  
% 3.38/0.99  fof(f44,plain,(
% 3.38/0.99    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.38/0.99    inference(cnf_transformation,[],[f18])).
% 3.38/0.99  
% 3.38/0.99  fof(f7,axiom,(
% 3.38/0.99    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 3.38/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/0.99  
% 3.38/0.99  fof(f17,plain,(
% 3.38/0.99    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.38/0.99    inference(ennf_transformation,[],[f7])).
% 3.38/0.99  
% 3.38/0.99  fof(f43,plain,(
% 3.38/0.99    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.38/0.99    inference(cnf_transformation,[],[f17])).
% 3.38/0.99  
% 3.38/0.99  fof(f11,axiom,(
% 3.38/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.38/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/0.99  
% 3.38/0.99  fof(f22,plain,(
% 3.38/0.99    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.38/0.99    inference(ennf_transformation,[],[f11])).
% 3.38/0.99  
% 3.38/0.99  fof(f47,plain,(
% 3.38/0.99    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.38/0.99    inference(cnf_transformation,[],[f22])).
% 3.38/0.99  
% 3.38/0.99  fof(f58,plain,(
% 3.38/0.99    ~r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1)))),
% 3.38/0.99    inference(cnf_transformation,[],[f33])).
% 3.38/0.99  
% 3.38/0.99  fof(f66,plain,(
% 3.38/0.99    ~r1_tarski(k7_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4,sK3),k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)))),
% 3.38/0.99    inference(definition_unfolding,[],[f58,f59,f59])).
% 3.38/0.99  
% 3.38/0.99  cnf(c_21,negated_conjecture,
% 3.38/0.99      ( v1_funct_2(sK4,k1_enumset1(sK1,sK1,sK1),sK2) ),
% 3.38/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_17,plain,
% 3.38/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.38/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.38/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.38/0.99      | k1_xboole_0 = X2 ),
% 3.38/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_20,negated_conjecture,
% 3.38/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))) ),
% 3.38/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_388,plain,
% 3.38/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.38/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.38/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 3.38/0.99      | sK4 != X0
% 3.38/0.99      | k1_xboole_0 = X2 ),
% 3.38/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_20]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_389,plain,
% 3.38/0.99      ( ~ v1_funct_2(sK4,X0,X1)
% 3.38/0.99      | k1_relset_1(X0,X1,sK4) = X0
% 3.38/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.38/0.99      | k1_xboole_0 = X1 ),
% 3.38/0.99      inference(unflattening,[status(thm)],[c_388]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_551,plain,
% 3.38/0.99      ( k1_relset_1(X0,X1,sK4) = X0
% 3.38/0.99      | k1_enumset1(sK1,sK1,sK1) != X0
% 3.38/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.38/0.99      | sK4 != sK4
% 3.38/0.99      | sK2 != X1
% 3.38/0.99      | k1_xboole_0 = X1 ),
% 3.38/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_389]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_552,plain,
% 3.38/0.99      ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4) = k1_enumset1(sK1,sK1,sK1)
% 3.38/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))
% 3.38/0.99      | k1_xboole_0 = sK2 ),
% 3.38/0.99      inference(unflattening,[status(thm)],[c_551]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_19,negated_conjecture,
% 3.38/0.99      ( k1_xboole_0 != sK2 ),
% 3.38/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_553,plain,
% 3.38/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))
% 3.38/0.99      | k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4) = k1_enumset1(sK1,sK1,sK1) ),
% 3.38/0.99      inference(global_propositional_subsumption,
% 3.38/0.99                [status(thm)],
% 3.38/0.99                [c_552,c_19]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_554,plain,
% 3.38/0.99      ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4) = k1_enumset1(sK1,sK1,sK1)
% 3.38/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
% 3.38/0.99      inference(renaming,[status(thm)],[c_553]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_614,plain,
% 3.38/0.99      ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4) = k1_enumset1(sK1,sK1,sK1) ),
% 3.38/0.99      inference(equality_resolution_simp,[status(thm)],[c_554]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_10,plain,
% 3.38/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.38/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.38/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_433,plain,
% 3.38/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.38/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.38/0.99      | sK4 != X2 ),
% 3.38/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_20]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_434,plain,
% 3.38/0.99      ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
% 3.38/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 3.38/0.99      inference(unflattening,[status(thm)],[c_433]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_1098,plain,
% 3.38/0.99      ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4) = k1_relat_1(sK4) ),
% 3.38/0.99      inference(equality_resolution,[status(thm)],[c_434]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_1272,plain,
% 3.38/0.99      ( k1_enumset1(sK1,sK1,sK1) = k1_relat_1(sK4) ),
% 3.38/0.99      inference(light_normalisation,[status(thm)],[c_614,c_1098]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_2,plain,
% 3.38/0.99      ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) ),
% 3.38/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_1006,plain,
% 3.38/0.99      ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) = iProver_top ),
% 3.38/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_1387,plain,
% 3.38/0.99      ( r2_hidden(sK1,k1_relat_1(sK4)) = iProver_top ),
% 3.38/0.99      inference(superposition,[status(thm)],[c_1272,c_1006]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_9,plain,
% 3.38/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.38/0.99      | ~ v1_funct_1(X1)
% 3.38/0.99      | ~ v1_relat_1(X1)
% 3.38/0.99      | k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ),
% 3.38/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_22,negated_conjecture,
% 3.38/0.99      ( v1_funct_1(sK4) ),
% 3.38/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_272,plain,
% 3.38/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.38/0.99      | ~ v1_relat_1(X1)
% 3.38/0.99      | k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
% 3.38/0.99      | sK4 != X1 ),
% 3.38/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_22]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_273,plain,
% 3.38/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 3.38/0.99      | ~ v1_relat_1(sK4)
% 3.38/0.99      | k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0) ),
% 3.38/0.99      inference(unflattening,[status(thm)],[c_272]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_999,plain,
% 3.38/0.99      ( k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0)
% 3.38/0.99      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 3.38/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.38/0.99      inference(predicate_to_equality,[status(thm)],[c_273]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_274,plain,
% 3.38/0.99      ( k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0)
% 3.38/0.99      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 3.38/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.38/0.99      inference(predicate_to_equality,[status(thm)],[c_273]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_4,plain,
% 3.38/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.38/0.99      | ~ v1_relat_1(X1)
% 3.38/0.99      | v1_relat_1(X0) ),
% 3.38/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_373,plain,
% 3.38/0.99      ( ~ v1_relat_1(X0)
% 3.38/0.99      | v1_relat_1(X1)
% 3.38/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(X0)
% 3.38/0.99      | sK4 != X1 ),
% 3.38/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_20]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_374,plain,
% 3.38/0.99      ( ~ v1_relat_1(X0)
% 3.38/0.99      | v1_relat_1(sK4)
% 3.38/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(X0) ),
% 3.38/0.99      inference(unflattening,[status(thm)],[c_373]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_1049,plain,
% 3.38/0.99      ( ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 3.38/0.99      | v1_relat_1(sK4)
% 3.38/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 3.38/0.99      inference(instantiation,[status(thm)],[c_374]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_1117,plain,
% 3.38/0.99      ( ~ v1_relat_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))
% 3.38/0.99      | v1_relat_1(sK4)
% 3.38/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
% 3.38/0.99      inference(instantiation,[status(thm)],[c_1049]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_1118,plain,
% 3.38/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))
% 3.38/0.99      | v1_relat_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != iProver_top
% 3.38/0.99      | v1_relat_1(sK4) = iProver_top ),
% 3.38/0.99      inference(predicate_to_equality,[status(thm)],[c_1117]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_780,plain,( X0 = X0 ),theory(equality) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_1164,plain,
% 3.38/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) = k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
% 3.38/0.99      inference(instantiation,[status(thm)],[c_780]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_6,plain,
% 3.38/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.38/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_1182,plain,
% 3.38/0.99      ( v1_relat_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
% 3.38/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_1183,plain,
% 3.38/0.99      ( v1_relat_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) = iProver_top ),
% 3.38/0.99      inference(predicate_to_equality,[status(thm)],[c_1182]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_1888,plain,
% 3.38/0.99      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 3.38/0.99      | k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0) ),
% 3.38/0.99      inference(global_propositional_subsumption,
% 3.38/0.99                [status(thm)],
% 3.38/0.99                [c_999,c_274,c_1118,c_1164,c_1183]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_1889,plain,
% 3.38/0.99      ( k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0)
% 3.38/0.99      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
% 3.38/0.99      inference(renaming,[status(thm)],[c_1888]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_2057,plain,
% 3.38/0.99      ( k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) = k11_relat_1(sK4,sK1) ),
% 3.38/0.99      inference(superposition,[status(thm)],[c_1387,c_1889]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_998,plain,
% 3.38/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(X0)
% 3.38/0.99      | v1_relat_1(X0) != iProver_top
% 3.38/0.99      | v1_relat_1(sK4) = iProver_top ),
% 3.38/0.99      inference(predicate_to_equality,[status(thm)],[c_374]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_1315,plain,
% 3.38/0.99      ( v1_relat_1(sK4) = iProver_top ),
% 3.38/0.99      inference(global_propositional_subsumption,
% 3.38/0.99                [status(thm)],
% 3.38/0.99                [c_998,c_1118,c_1164,c_1183]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_5,plain,
% 3.38/0.99      ( ~ v1_relat_1(X0)
% 3.38/0.99      | k9_relat_1(X0,k1_enumset1(X1,X1,X1)) = k11_relat_1(X0,X1) ),
% 3.38/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_1004,plain,
% 3.38/0.99      ( k9_relat_1(X0,k1_enumset1(X1,X1,X1)) = k11_relat_1(X0,X1)
% 3.38/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.38/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_2018,plain,
% 3.38/0.99      ( k9_relat_1(sK4,k1_enumset1(X0,X0,X0)) = k11_relat_1(sK4,X0) ),
% 3.38/0.99      inference(superposition,[status(thm)],[c_1315,c_1004]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_2104,plain,
% 3.38/0.99      ( k9_relat_1(sK4,k1_relat_1(sK4)) = k11_relat_1(sK4,sK1) ),
% 3.38/0.99      inference(superposition,[status(thm)],[c_1272,c_2018]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_8,plain,
% 3.38/0.99      ( ~ v1_relat_1(X0)
% 3.38/0.99      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 3.38/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_1001,plain,
% 3.38/0.99      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 3.38/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.38/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_1391,plain,
% 3.38/0.99      ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4) ),
% 3.38/0.99      inference(superposition,[status(thm)],[c_1315,c_1001]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_2106,plain,
% 3.38/0.99      ( k11_relat_1(sK4,sK1) = k2_relat_1(sK4) ),
% 3.38/0.99      inference(light_normalisation,[status(thm)],[c_2104,c_1391]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_2110,plain,
% 3.38/0.99      ( k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) = k2_relat_1(sK4) ),
% 3.38/0.99      inference(light_normalisation,[status(thm)],[c_2057,c_2057,c_2106]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_7,plain,
% 3.38/0.99      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 3.38/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_1382,plain,
% 3.38/0.99      ( r1_tarski(k9_relat_1(sK4,sK3),k2_relat_1(sK4))
% 3.38/0.99      | ~ v1_relat_1(sK4) ),
% 3.38/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_789,plain,
% 3.38/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.38/0.99      theory(equality) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_1023,plain,
% 3.38/0.99      ( ~ r1_tarski(X0,X1)
% 3.38/0.99      | r1_tarski(k7_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4,sK3),k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)))
% 3.38/0.99      | k7_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4,sK3) != X0
% 3.38/0.99      | k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) != X1 ),
% 3.38/0.99      inference(instantiation,[status(thm)],[c_789]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_1152,plain,
% 3.38/0.99      ( r1_tarski(k7_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4,sK3),k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)))
% 3.38/0.99      | ~ r1_tarski(k9_relat_1(sK4,sK3),X0)
% 3.38/0.99      | k7_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4,sK3) != k9_relat_1(sK4,sK3)
% 3.38/0.99      | k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) != X0 ),
% 3.38/0.99      inference(instantiation,[status(thm)],[c_1023]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_1302,plain,
% 3.38/0.99      ( r1_tarski(k7_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4,sK3),k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)))
% 3.38/0.99      | ~ r1_tarski(k9_relat_1(sK4,sK3),k2_relat_1(sK4))
% 3.38/0.99      | k7_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4,sK3) != k9_relat_1(sK4,sK3)
% 3.38/0.99      | k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) != k2_relat_1(sK4) ),
% 3.38/0.99      inference(instantiation,[status(thm)],[c_1152]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_11,plain,
% 3.38/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.38/0.99      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.38/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_424,plain,
% 3.38/0.99      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.38/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.38/0.99      | sK4 != X2 ),
% 3.38/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_20]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_425,plain,
% 3.38/0.99      ( k7_relset_1(X0,X1,sK4,X2) = k9_relat_1(sK4,X2)
% 3.38/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 3.38/0.99      inference(unflattening,[status(thm)],[c_424]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_1101,plain,
% 3.38/0.99      ( k7_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4,X0) = k9_relat_1(sK4,X0)
% 3.38/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
% 3.38/0.99      inference(instantiation,[status(thm)],[c_425]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_1151,plain,
% 3.38/0.99      ( k7_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4,sK3) = k9_relat_1(sK4,sK3)
% 3.38/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
% 3.38/0.99      inference(instantiation,[status(thm)],[c_1101]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_18,negated_conjecture,
% 3.38/0.99      ( ~ r1_tarski(k7_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4,sK3),k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) ),
% 3.38/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(contradiction,plain,
% 3.38/0.99      ( $false ),
% 3.38/0.99      inference(minisat,
% 3.38/0.99                [status(thm)],
% 3.38/0.99                [c_2110,c_1382,c_1302,c_1182,c_1164,c_1151,c_1117,c_18]) ).
% 3.38/0.99  
% 3.38/0.99  
% 3.38/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.38/0.99  
% 3.38/0.99  ------                               Statistics
% 3.38/0.99  
% 3.38/0.99  ------ General
% 3.38/0.99  
% 3.38/0.99  abstr_ref_over_cycles:                  0
% 3.38/0.99  abstr_ref_under_cycles:                 0
% 3.38/0.99  gc_basic_clause_elim:                   0
% 3.38/0.99  forced_gc_time:                         0
% 3.38/0.99  parsing_time:                           0.012
% 3.38/0.99  unif_index_cands_time:                  0.
% 3.38/0.99  unif_index_add_time:                    0.
% 3.38/0.99  orderings_time:                         0.
% 3.38/0.99  out_proof_time:                         0.023
% 3.38/0.99  total_time:                             0.135
% 3.38/0.99  num_of_symbols:                         53
% 3.38/0.99  num_of_terms:                           2050
% 3.38/0.99  
% 3.38/0.99  ------ Preprocessing
% 3.38/0.99  
% 3.38/0.99  num_of_splits:                          0
% 3.38/0.99  num_of_split_atoms:                     0
% 3.38/0.99  num_of_reused_defs:                     0
% 3.38/0.99  num_eq_ax_congr_red:                    17
% 3.38/0.99  num_of_sem_filtered_clauses:            1
% 3.38/0.99  num_of_subtypes:                        0
% 3.38/0.99  monotx_restored_types:                  0
% 3.38/0.99  sat_num_of_epr_types:                   0
% 3.38/0.99  sat_num_of_non_cyclic_types:            0
% 3.38/0.99  sat_guarded_non_collapsed_types:        0
% 3.38/0.99  num_pure_diseq_elim:                    0
% 3.38/0.99  simp_replaced_by:                       0
% 3.38/0.99  res_preprocessed:                       103
% 3.38/0.99  prep_upred:                             0
% 3.38/0.99  prep_unflattend:                        40
% 3.38/0.99  smt_new_axioms:                         0
% 3.38/0.99  pred_elim_cands:                        3
% 3.38/0.99  pred_elim:                              3
% 3.38/0.99  pred_elim_cl:                           6
% 3.38/0.99  pred_elim_cycles:                       8
% 3.38/0.99  merged_defs:                            0
% 3.38/0.99  merged_defs_ncl:                        0
% 3.38/0.99  bin_hyper_res:                          0
% 3.38/0.99  prep_cycles:                            4
% 3.38/0.99  pred_elim_time:                         0.009
% 3.38/0.99  splitting_time:                         0.
% 3.38/0.99  sem_filter_time:                        0.
% 3.38/0.99  monotx_time:                            0.
% 3.38/0.99  subtype_inf_time:                       0.
% 3.38/0.99  
% 3.38/0.99  ------ Problem properties
% 3.38/0.99  
% 3.38/0.99  clauses:                                17
% 3.38/0.99  conjectures:                            2
% 3.38/0.99  epr:                                    1
% 3.38/0.99  horn:                                   15
% 3.38/0.99  ground:                                 5
% 3.38/0.99  unary:                                  5
% 3.38/0.99  binary:                                 6
% 3.38/0.99  lits:                                   36
% 3.38/0.99  lits_eq:                                22
% 3.38/0.99  fd_pure:                                0
% 3.38/0.99  fd_pseudo:                              0
% 3.38/0.99  fd_cond:                                0
% 3.38/0.99  fd_pseudo_cond:                         2
% 3.38/0.99  ac_symbols:                             0
% 3.38/0.99  
% 3.38/0.99  ------ Propositional Solver
% 3.38/0.99  
% 3.38/0.99  prop_solver_calls:                      27
% 3.38/0.99  prop_fast_solver_calls:                 634
% 3.38/0.99  smt_solver_calls:                       0
% 3.38/0.99  smt_fast_solver_calls:                  0
% 3.38/0.99  prop_num_of_clauses:                    759
% 3.38/0.99  prop_preprocess_simplified:             3348
% 3.38/0.99  prop_fo_subsumed:                       7
% 3.38/0.99  prop_solver_time:                       0.
% 3.38/0.99  smt_solver_time:                        0.
% 3.38/0.99  smt_fast_solver_time:                   0.
% 3.38/0.99  prop_fast_solver_time:                  0.
% 3.38/0.99  prop_unsat_core_time:                   0.
% 3.38/0.99  
% 3.38/0.99  ------ QBF
% 3.38/0.99  
% 3.38/0.99  qbf_q_res:                              0
% 3.38/0.99  qbf_num_tautologies:                    0
% 3.38/0.99  qbf_prep_cycles:                        0
% 3.38/0.99  
% 3.38/0.99  ------ BMC1
% 3.38/0.99  
% 3.38/0.99  bmc1_current_bound:                     -1
% 3.38/0.99  bmc1_last_solved_bound:                 -1
% 3.38/0.99  bmc1_unsat_core_size:                   -1
% 3.38/0.99  bmc1_unsat_core_parents_size:           -1
% 3.38/0.99  bmc1_merge_next_fun:                    0
% 3.38/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.38/0.99  
% 3.38/0.99  ------ Instantiation
% 3.38/0.99  
% 3.38/0.99  inst_num_of_clauses:                    232
% 3.38/0.99  inst_num_in_passive:                    59
% 3.38/0.99  inst_num_in_active:                     120
% 3.38/0.99  inst_num_in_unprocessed:                53
% 3.38/0.99  inst_num_of_loops:                      140
% 3.38/0.99  inst_num_of_learning_restarts:          0
% 3.38/0.99  inst_num_moves_active_passive:          18
% 3.38/0.99  inst_lit_activity:                      0
% 3.38/0.99  inst_lit_activity_moves:                0
% 3.38/0.99  inst_num_tautologies:                   0
% 3.38/0.99  inst_num_prop_implied:                  0
% 3.38/0.99  inst_num_existing_simplified:           0
% 3.38/0.99  inst_num_eq_res_simplified:             0
% 3.38/0.99  inst_num_child_elim:                    0
% 3.38/0.99  inst_num_of_dismatching_blockings:      59
% 3.38/0.99  inst_num_of_non_proper_insts:           222
% 3.38/0.99  inst_num_of_duplicates:                 0
% 3.38/0.99  inst_inst_num_from_inst_to_res:         0
% 3.38/0.99  inst_dismatching_checking_time:         0.
% 3.38/0.99  
% 3.38/0.99  ------ Resolution
% 3.38/0.99  
% 3.38/0.99  res_num_of_clauses:                     0
% 3.38/0.99  res_num_in_passive:                     0
% 3.38/0.99  res_num_in_active:                      0
% 3.38/0.99  res_num_of_loops:                       107
% 3.38/0.99  res_forward_subset_subsumed:            32
% 3.38/0.99  res_backward_subset_subsumed:           0
% 3.38/0.99  res_forward_subsumed:                   0
% 3.38/0.99  res_backward_subsumed:                  0
% 3.38/0.99  res_forward_subsumption_resolution:     0
% 3.38/0.99  res_backward_subsumption_resolution:    0
% 3.38/0.99  res_clause_to_clause_subsumption:       55
% 3.38/0.99  res_orphan_elimination:                 0
% 3.38/0.99  res_tautology_del:                      19
% 3.38/0.99  res_num_eq_res_simplified:              1
% 3.38/0.99  res_num_sel_changes:                    0
% 3.38/0.99  res_moves_from_active_to_pass:          0
% 3.38/0.99  
% 3.38/0.99  ------ Superposition
% 3.38/0.99  
% 3.38/0.99  sup_time_total:                         0.
% 3.38/0.99  sup_time_generating:                    0.
% 3.38/0.99  sup_time_sim_full:                      0.
% 3.38/0.99  sup_time_sim_immed:                     0.
% 3.38/0.99  
% 3.38/0.99  sup_num_of_clauses:                     30
% 3.38/0.99  sup_num_in_active:                      22
% 3.38/0.99  sup_num_in_passive:                     8
% 3.38/0.99  sup_num_of_loops:                       27
% 3.38/0.99  sup_fw_superposition:                   9
% 3.38/0.99  sup_bw_superposition:                   4
% 3.38/0.99  sup_immediate_simplified:               1
% 3.38/0.99  sup_given_eliminated:                   0
% 3.38/0.99  comparisons_done:                       0
% 3.38/0.99  comparisons_avoided:                    2
% 3.38/0.99  
% 3.38/0.99  ------ Simplifications
% 3.38/0.99  
% 3.38/0.99  
% 3.38/0.99  sim_fw_subset_subsumed:                 0
% 3.38/0.99  sim_bw_subset_subsumed:                 0
% 3.38/0.99  sim_fw_subsumed:                        0
% 3.38/0.99  sim_bw_subsumed:                        0
% 3.38/0.99  sim_fw_subsumption_res:                 0
% 3.38/0.99  sim_bw_subsumption_res:                 0
% 3.38/0.99  sim_tautology_del:                      0
% 3.38/0.99  sim_eq_tautology_del:                   1
% 3.38/0.99  sim_eq_res_simp:                        0
% 3.38/0.99  sim_fw_demodulated:                     1
% 3.38/0.99  sim_bw_demodulated:                     5
% 3.38/0.99  sim_light_normalised:                   4
% 3.38/0.99  sim_joinable_taut:                      0
% 3.38/0.99  sim_joinable_simp:                      0
% 3.38/0.99  sim_ac_normalised:                      0
% 3.38/0.99  sim_smt_subsumption:                    0
% 3.38/0.99  
%------------------------------------------------------------------------------
