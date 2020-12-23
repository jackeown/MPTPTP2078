%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:10 EST 2020

% Result     : Theorem 3.04s
% Output     : CNFRefutation 3.04s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 748 expanded)
%              Number of clauses        :   73 ( 200 expanded)
%              Number of leaves         :   16 ( 171 expanded)
%              Depth                    :   19
%              Number of atoms          :  365 (2158 expanded)
%              Number of equality atoms :  207 (1050 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f35,plain,
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

fof(f36,plain,
    ( k1_tarski(k1_funct_1(sK3,sK1)) != k2_relset_1(k1_tarski(sK1),sK2,sK3)
    & k1_xboole_0 != sK2
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
    & v1_funct_2(sK3,k1_tarski(sK1),sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f29,f35])).

fof(f59,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) ),
    inference(cnf_transformation,[],[f36])).

fof(f2,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f62,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f41,f42])).

fof(f70,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))) ),
    inference(definition_unfolding,[],[f59,f62])).

fof(f58,plain,(
    v1_funct_2(sK3,k1_tarski(sK1),sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f71,plain,(
    v1_funct_2(sK3,k1_enumset1(sK1,sK1,sK1),sK2) ),
    inference(definition_unfolding,[],[f58,f62])).

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

fof(f26,plain,(
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
    inference(flattening,[],[f26])).

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
    inference(nnf_transformation,[],[f27])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f60,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
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

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f32,plain,(
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

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f38,f62])).

fof(f72,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_enumset1(X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f65])).

fof(f73,plain,(
    ! [X3] : r2_hidden(X3,k1_enumset1(X3,X3,X3)) ),
    inference(equality_resolution,[],[f72])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f46,f62])).

fof(f57,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_enumset1(X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f43,f62])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f61,plain,(
    k1_tarski(k1_funct_1(sK3,sK1)) != k2_relset_1(k1_tarski(sK1),sK2,sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f69,plain,(
    k1_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK3) ),
    inference(definition_unfolding,[],[f61,f62,f62])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_468,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_20])).

cnf(c_469,plain,
    ( k1_relset_1(X0,X1,sK3) = k1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_468])).

cnf(c_1290,plain,
    ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK3) = k1_relat_1(sK3) ),
    inference(equality_resolution,[status(thm)],[c_469])).

cnf(c_21,negated_conjecture,
    ( v1_funct_2(sK3,k1_enumset1(sK1,sK1,sK1),sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_423,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_20])).

cnf(c_424,plain,
    ( ~ v1_funct_2(sK3,X0,X1)
    | k1_relset_1(X0,X1,sK3) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_423])).

cnf(c_712,plain,
    ( k1_relset_1(X0,X1,sK3) = X0
    | k1_enumset1(sK1,sK1,sK1) != X0
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK2 != X1
    | sK3 != sK3
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_424])).

cnf(c_713,plain,
    ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK3) = k1_enumset1(sK1,sK1,sK1)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_712])).

cnf(c_19,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_714,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))
    | k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK3) = k1_enumset1(sK1,sK1,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_713,c_19])).

cnf(c_715,plain,
    ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK3) = k1_enumset1(sK1,sK1,sK1)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
    inference(renaming,[status(thm)],[c_714])).

cnf(c_769,plain,
    ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK3) = k1_enumset1(sK1,sK1,sK1) ),
    inference(equality_resolution_simp,[status(thm)],[c_715])).

cnf(c_1484,plain,
    ( k1_enumset1(sK1,sK1,sK1) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_1290,c_769])).

cnf(c_2,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1123,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1554,plain,
    ( r2_hidden(sK1,k1_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1484,c_1123])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_477,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_20])).

cnf(c_478,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_477])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_269,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_22])).

cnf(c_270,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_269])).

cnf(c_591,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
    inference(resolution,[status(thm)],[c_478,c_270])).

cnf(c_887,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
    | ~ sP3_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP3_iProver_split])],[c_591])).

cnf(c_1120,plain,
    ( k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | sP3_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_887])).

cnf(c_888,plain,
    ( sP3_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_591])).

cnf(c_930,plain,
    ( sP3_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_888])).

cnf(c_931,plain,
    ( k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | sP3_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_887])).

cnf(c_890,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1231,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) = k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_890])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_enumset1(X1,X1,X1)) = k11_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_614,plain,
    ( k9_relat_1(X0,k1_enumset1(X1,X1,X1)) = k11_relat_1(X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_478])).

cnf(c_615,plain,
    ( k9_relat_1(sK3,k1_enumset1(X0,X0,X0)) = k11_relat_1(sK3,X0)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
    inference(unflattening,[status(thm)],[c_614])).

cnf(c_882,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_615])).

cnf(c_1232,plain,
    ( ~ sP0_iProver_split
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_882])).

cnf(c_1236,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1232])).

cnf(c_2353,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1120,c_930,c_931,c_1231,c_1236])).

cnf(c_2354,plain,
    ( k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2353])).

cnf(c_2362,plain,
    ( k1_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) = k11_relat_1(sK3,sK1) ),
    inference(superposition,[status(thm)],[c_1554,c_2354])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_459,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_20])).

cnf(c_460,plain,
    ( k2_relset_1(X0,X1,sK3) = k2_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_459])).

cnf(c_1245,plain,
    ( k2_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK3) = k2_relat_1(sK3) ),
    inference(equality_resolution,[status(thm)],[c_460])).

cnf(c_18,negated_conjecture,
    ( k1_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1444,plain,
    ( k1_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_1245,c_18])).

cnf(c_11695,plain,
    ( k11_relat_1(sK3,sK1) != k2_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_2362,c_1444])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_6,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_249,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_9,c_6])).

cnf(c_253,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_249,c_9,c_8,c_6])).

cnf(c_414,plain,
    ( k7_relat_1(X0,X1) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_253,c_20])).

cnf(c_415,plain,
    ( k7_relat_1(sK3,X0) = sK3
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_414])).

cnf(c_1242,plain,
    ( k7_relat_1(sK3,k1_enumset1(sK1,sK1,sK1)) = sK3 ),
    inference(equality_resolution,[status(thm)],[c_415])).

cnf(c_1522,plain,
    ( k7_relat_1(sK3,k1_relat_1(sK3)) = sK3 ),
    inference(demodulation,[status(thm)],[c_1484,c_1242])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_605,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k2_relat_1(k7_relat_1(X2,X3)) = k9_relat_1(X2,X3)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_478])).

cnf(c_606,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k2_relat_1(k7_relat_1(sK3,X2)) = k9_relat_1(sK3,X2) ),
    inference(unflattening,[status(thm)],[c_605])).

cnf(c_885,plain,
    ( k2_relat_1(k7_relat_1(sK3,X0)) = k9_relat_1(sK3,X0)
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_606])).

cnf(c_1118,plain,
    ( k2_relat_1(k7_relat_1(sK3,X0)) = k9_relat_1(sK3,X0)
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_885])).

cnf(c_886,plain,
    ( sP2_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_606])).

cnf(c_2254,plain,
    ( k2_relat_1(k7_relat_1(sK3,X0)) = k9_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1118,c_886,c_885,c_1231,c_1232])).

cnf(c_2258,plain,
    ( k9_relat_1(sK3,k1_relat_1(sK3)) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1522,c_2254])).

cnf(c_883,plain,
    ( k9_relat_1(sK3,k1_enumset1(X0,X0,X0)) = k11_relat_1(sK3,X0)
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_615])).

cnf(c_1114,plain,
    ( k9_relat_1(sK3,k1_enumset1(X0,X0,X0)) = k11_relat_1(sK3,X0)
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_883])).

cnf(c_884,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_615])).

cnf(c_1849,plain,
    ( k9_relat_1(sK3,k1_enumset1(X0,X0,X0)) = k11_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1114,c_884,c_883,c_1231,c_1232])).

cnf(c_1853,plain,
    ( k9_relat_1(sK3,k1_relat_1(sK3)) = k11_relat_1(sK3,sK1) ),
    inference(superposition,[status(thm)],[c_1484,c_1849])).

cnf(c_9616,plain,
    ( k11_relat_1(sK3,sK1) = k2_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_2258,c_1853])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11695,c_9616])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:11:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.04/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.04/0.98  
% 3.04/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.04/0.98  
% 3.04/0.98  ------  iProver source info
% 3.04/0.98  
% 3.04/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.04/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.04/0.98  git: non_committed_changes: false
% 3.04/0.98  git: last_make_outside_of_git: false
% 3.04/0.98  
% 3.04/0.98  ------ 
% 3.04/0.98  
% 3.04/0.98  ------ Input Options
% 3.04/0.98  
% 3.04/0.98  --out_options                           all
% 3.04/0.98  --tptp_safe_out                         true
% 3.04/0.98  --problem_path                          ""
% 3.04/0.98  --include_path                          ""
% 3.04/0.98  --clausifier                            res/vclausify_rel
% 3.04/0.98  --clausifier_options                    --mode clausify
% 3.04/0.98  --stdin                                 false
% 3.04/0.98  --stats_out                             all
% 3.04/0.98  
% 3.04/0.98  ------ General Options
% 3.04/0.98  
% 3.04/0.98  --fof                                   false
% 3.04/0.98  --time_out_real                         305.
% 3.04/0.98  --time_out_virtual                      -1.
% 3.04/0.98  --symbol_type_check                     false
% 3.04/0.98  --clausify_out                          false
% 3.04/0.98  --sig_cnt_out                           false
% 3.04/0.98  --trig_cnt_out                          false
% 3.04/0.98  --trig_cnt_out_tolerance                1.
% 3.04/0.98  --trig_cnt_out_sk_spl                   false
% 3.04/0.98  --abstr_cl_out                          false
% 3.04/0.98  
% 3.04/0.98  ------ Global Options
% 3.04/0.98  
% 3.04/0.98  --schedule                              default
% 3.04/0.98  --add_important_lit                     false
% 3.04/0.98  --prop_solver_per_cl                    1000
% 3.04/0.98  --min_unsat_core                        false
% 3.04/0.98  --soft_assumptions                      false
% 3.04/0.98  --soft_lemma_size                       3
% 3.04/0.98  --prop_impl_unit_size                   0
% 3.04/0.98  --prop_impl_unit                        []
% 3.04/0.98  --share_sel_clauses                     true
% 3.04/0.98  --reset_solvers                         false
% 3.04/0.98  --bc_imp_inh                            [conj_cone]
% 3.04/0.98  --conj_cone_tolerance                   3.
% 3.04/0.98  --extra_neg_conj                        none
% 3.04/0.98  --large_theory_mode                     true
% 3.04/0.98  --prolific_symb_bound                   200
% 3.04/0.98  --lt_threshold                          2000
% 3.04/0.98  --clause_weak_htbl                      true
% 3.04/0.98  --gc_record_bc_elim                     false
% 3.04/0.98  
% 3.04/0.98  ------ Preprocessing Options
% 3.04/0.98  
% 3.04/0.98  --preprocessing_flag                    true
% 3.04/0.98  --time_out_prep_mult                    0.1
% 3.04/0.98  --splitting_mode                        input
% 3.04/0.98  --splitting_grd                         true
% 3.04/0.98  --splitting_cvd                         false
% 3.04/0.98  --splitting_cvd_svl                     false
% 3.04/0.98  --splitting_nvd                         32
% 3.04/0.98  --sub_typing                            true
% 3.04/0.98  --prep_gs_sim                           true
% 3.04/0.98  --prep_unflatten                        true
% 3.04/0.98  --prep_res_sim                          true
% 3.04/0.98  --prep_upred                            true
% 3.04/0.98  --prep_sem_filter                       exhaustive
% 3.04/0.98  --prep_sem_filter_out                   false
% 3.04/0.98  --pred_elim                             true
% 3.04/0.98  --res_sim_input                         true
% 3.04/0.98  --eq_ax_congr_red                       true
% 3.04/0.98  --pure_diseq_elim                       true
% 3.04/0.98  --brand_transform                       false
% 3.04/0.98  --non_eq_to_eq                          false
% 3.04/0.98  --prep_def_merge                        true
% 3.04/0.98  --prep_def_merge_prop_impl              false
% 3.04/0.98  --prep_def_merge_mbd                    true
% 3.04/0.98  --prep_def_merge_tr_red                 false
% 3.04/0.98  --prep_def_merge_tr_cl                  false
% 3.04/0.98  --smt_preprocessing                     true
% 3.04/0.98  --smt_ac_axioms                         fast
% 3.04/0.98  --preprocessed_out                      false
% 3.04/0.98  --preprocessed_stats                    false
% 3.04/0.98  
% 3.04/0.98  ------ Abstraction refinement Options
% 3.04/0.98  
% 3.04/0.98  --abstr_ref                             []
% 3.04/0.98  --abstr_ref_prep                        false
% 3.04/0.98  --abstr_ref_until_sat                   false
% 3.04/0.98  --abstr_ref_sig_restrict                funpre
% 3.04/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.04/0.98  --abstr_ref_under                       []
% 3.04/0.98  
% 3.04/0.98  ------ SAT Options
% 3.04/0.98  
% 3.04/0.98  --sat_mode                              false
% 3.04/0.98  --sat_fm_restart_options                ""
% 3.04/0.98  --sat_gr_def                            false
% 3.04/0.98  --sat_epr_types                         true
% 3.04/0.98  --sat_non_cyclic_types                  false
% 3.04/0.98  --sat_finite_models                     false
% 3.04/0.98  --sat_fm_lemmas                         false
% 3.04/0.98  --sat_fm_prep                           false
% 3.04/0.98  --sat_fm_uc_incr                        true
% 3.04/0.98  --sat_out_model                         small
% 3.04/0.98  --sat_out_clauses                       false
% 3.04/0.98  
% 3.04/0.98  ------ QBF Options
% 3.04/0.98  
% 3.04/0.98  --qbf_mode                              false
% 3.04/0.98  --qbf_elim_univ                         false
% 3.04/0.98  --qbf_dom_inst                          none
% 3.04/0.98  --qbf_dom_pre_inst                      false
% 3.04/0.98  --qbf_sk_in                             false
% 3.04/0.98  --qbf_pred_elim                         true
% 3.04/0.98  --qbf_split                             512
% 3.04/0.98  
% 3.04/0.98  ------ BMC1 Options
% 3.04/0.98  
% 3.04/0.98  --bmc1_incremental                      false
% 3.04/0.98  --bmc1_axioms                           reachable_all
% 3.04/0.98  --bmc1_min_bound                        0
% 3.04/0.98  --bmc1_max_bound                        -1
% 3.04/0.98  --bmc1_max_bound_default                -1
% 3.04/0.98  --bmc1_symbol_reachability              true
% 3.04/0.98  --bmc1_property_lemmas                  false
% 3.04/0.98  --bmc1_k_induction                      false
% 3.04/0.98  --bmc1_non_equiv_states                 false
% 3.04/0.98  --bmc1_deadlock                         false
% 3.04/0.98  --bmc1_ucm                              false
% 3.04/0.98  --bmc1_add_unsat_core                   none
% 3.04/0.98  --bmc1_unsat_core_children              false
% 3.04/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.04/0.98  --bmc1_out_stat                         full
% 3.04/0.98  --bmc1_ground_init                      false
% 3.04/0.98  --bmc1_pre_inst_next_state              false
% 3.04/0.98  --bmc1_pre_inst_state                   false
% 3.04/0.98  --bmc1_pre_inst_reach_state             false
% 3.04/0.98  --bmc1_out_unsat_core                   false
% 3.04/0.98  --bmc1_aig_witness_out                  false
% 3.04/0.98  --bmc1_verbose                          false
% 3.04/0.98  --bmc1_dump_clauses_tptp                false
% 3.04/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.04/0.98  --bmc1_dump_file                        -
% 3.04/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.04/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.04/0.98  --bmc1_ucm_extend_mode                  1
% 3.04/0.98  --bmc1_ucm_init_mode                    2
% 3.04/0.98  --bmc1_ucm_cone_mode                    none
% 3.04/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.04/0.98  --bmc1_ucm_relax_model                  4
% 3.04/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.04/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.04/0.98  --bmc1_ucm_layered_model                none
% 3.04/0.98  --bmc1_ucm_max_lemma_size               10
% 3.04/0.98  
% 3.04/0.98  ------ AIG Options
% 3.04/0.98  
% 3.04/0.98  --aig_mode                              false
% 3.04/0.98  
% 3.04/0.98  ------ Instantiation Options
% 3.04/0.98  
% 3.04/0.98  --instantiation_flag                    true
% 3.04/0.98  --inst_sos_flag                         false
% 3.04/0.98  --inst_sos_phase                        true
% 3.04/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.04/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.04/0.98  --inst_lit_sel_side                     num_symb
% 3.04/0.98  --inst_solver_per_active                1400
% 3.04/0.98  --inst_solver_calls_frac                1.
% 3.04/0.98  --inst_passive_queue_type               priority_queues
% 3.04/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.04/0.98  --inst_passive_queues_freq              [25;2]
% 3.04/0.98  --inst_dismatching                      true
% 3.04/0.98  --inst_eager_unprocessed_to_passive     true
% 3.04/0.98  --inst_prop_sim_given                   true
% 3.04/0.98  --inst_prop_sim_new                     false
% 3.04/0.98  --inst_subs_new                         false
% 3.04/0.98  --inst_eq_res_simp                      false
% 3.04/0.98  --inst_subs_given                       false
% 3.04/0.98  --inst_orphan_elimination               true
% 3.04/0.98  --inst_learning_loop_flag               true
% 3.04/0.98  --inst_learning_start                   3000
% 3.04/0.98  --inst_learning_factor                  2
% 3.04/0.98  --inst_start_prop_sim_after_learn       3
% 3.04/0.98  --inst_sel_renew                        solver
% 3.04/0.98  --inst_lit_activity_flag                true
% 3.04/0.98  --inst_restr_to_given                   false
% 3.04/0.98  --inst_activity_threshold               500
% 3.04/0.98  --inst_out_proof                        true
% 3.04/0.98  
% 3.04/0.98  ------ Resolution Options
% 3.04/0.98  
% 3.04/0.98  --resolution_flag                       true
% 3.04/0.98  --res_lit_sel                           adaptive
% 3.04/0.98  --res_lit_sel_side                      none
% 3.04/0.98  --res_ordering                          kbo
% 3.04/0.98  --res_to_prop_solver                    active
% 3.04/0.98  --res_prop_simpl_new                    false
% 3.04/0.98  --res_prop_simpl_given                  true
% 3.04/0.98  --res_passive_queue_type                priority_queues
% 3.04/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.04/0.98  --res_passive_queues_freq               [15;5]
% 3.04/0.98  --res_forward_subs                      full
% 3.04/0.98  --res_backward_subs                     full
% 3.04/0.98  --res_forward_subs_resolution           true
% 3.04/0.98  --res_backward_subs_resolution          true
% 3.04/0.98  --res_orphan_elimination                true
% 3.04/0.98  --res_time_limit                        2.
% 3.04/0.98  --res_out_proof                         true
% 3.04/0.98  
% 3.04/0.98  ------ Superposition Options
% 3.04/0.98  
% 3.04/0.98  --superposition_flag                    true
% 3.04/0.98  --sup_passive_queue_type                priority_queues
% 3.04/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.04/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.04/0.98  --demod_completeness_check              fast
% 3.04/0.98  --demod_use_ground                      true
% 3.04/0.98  --sup_to_prop_solver                    passive
% 3.04/0.98  --sup_prop_simpl_new                    true
% 3.04/0.98  --sup_prop_simpl_given                  true
% 3.04/0.98  --sup_fun_splitting                     false
% 3.04/0.98  --sup_smt_interval                      50000
% 3.04/0.98  
% 3.04/0.98  ------ Superposition Simplification Setup
% 3.04/0.98  
% 3.04/0.98  --sup_indices_passive                   []
% 3.04/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.04/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.98  --sup_full_bw                           [BwDemod]
% 3.04/0.98  --sup_immed_triv                        [TrivRules]
% 3.04/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.04/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.98  --sup_immed_bw_main                     []
% 3.04/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.04/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.04/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.04/0.98  
% 3.04/0.98  ------ Combination Options
% 3.04/0.98  
% 3.04/0.98  --comb_res_mult                         3
% 3.04/0.98  --comb_sup_mult                         2
% 3.04/0.98  --comb_inst_mult                        10
% 3.04/0.98  
% 3.04/0.98  ------ Debug Options
% 3.04/0.98  
% 3.04/0.98  --dbg_backtrace                         false
% 3.04/0.98  --dbg_dump_prop_clauses                 false
% 3.04/0.98  --dbg_dump_prop_clauses_file            -
% 3.04/0.98  --dbg_out_stat                          false
% 3.04/0.98  ------ Parsing...
% 3.04/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.04/0.98  
% 3.04/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.04/0.98  
% 3.04/0.98  ------ Preprocessing... gs_s  sp: 6 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.04/0.98  
% 3.04/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.04/0.98  ------ Proving...
% 3.04/0.98  ------ Problem Properties 
% 3.04/0.98  
% 3.04/0.98  
% 3.04/0.98  clauses                                 21
% 3.04/0.98  conjectures                             2
% 3.04/0.98  EPR                                     4
% 3.04/0.98  Horn                                    16
% 3.04/0.98  unary                                   4
% 3.04/0.98  binary                                  12
% 3.04/0.98  lits                                    44
% 3.04/0.98  lits eq                                 27
% 3.04/0.98  fd_pure                                 0
% 3.04/0.98  fd_pseudo                               0
% 3.04/0.98  fd_cond                                 0
% 3.04/0.98  fd_pseudo_cond                          2
% 3.04/0.98  AC symbols                              0
% 3.04/0.98  
% 3.04/0.98  ------ Schedule dynamic 5 is on 
% 3.04/0.98  
% 3.04/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.04/0.98  
% 3.04/0.98  
% 3.04/0.98  ------ 
% 3.04/0.98  Current options:
% 3.04/0.98  ------ 
% 3.04/0.98  
% 3.04/0.98  ------ Input Options
% 3.04/0.98  
% 3.04/0.98  --out_options                           all
% 3.04/0.98  --tptp_safe_out                         true
% 3.04/0.98  --problem_path                          ""
% 3.04/0.98  --include_path                          ""
% 3.04/0.98  --clausifier                            res/vclausify_rel
% 3.04/0.98  --clausifier_options                    --mode clausify
% 3.04/0.98  --stdin                                 false
% 3.04/0.98  --stats_out                             all
% 3.04/0.98  
% 3.04/0.98  ------ General Options
% 3.04/0.98  
% 3.04/0.98  --fof                                   false
% 3.04/0.98  --time_out_real                         305.
% 3.04/0.98  --time_out_virtual                      -1.
% 3.04/0.98  --symbol_type_check                     false
% 3.04/0.98  --clausify_out                          false
% 3.04/0.98  --sig_cnt_out                           false
% 3.04/0.98  --trig_cnt_out                          false
% 3.04/0.98  --trig_cnt_out_tolerance                1.
% 3.04/0.98  --trig_cnt_out_sk_spl                   false
% 3.04/0.98  --abstr_cl_out                          false
% 3.04/0.98  
% 3.04/0.98  ------ Global Options
% 3.04/0.98  
% 3.04/0.98  --schedule                              default
% 3.04/0.98  --add_important_lit                     false
% 3.04/0.98  --prop_solver_per_cl                    1000
% 3.04/0.98  --min_unsat_core                        false
% 3.04/0.98  --soft_assumptions                      false
% 3.04/0.98  --soft_lemma_size                       3
% 3.04/0.98  --prop_impl_unit_size                   0
% 3.04/0.98  --prop_impl_unit                        []
% 3.04/0.98  --share_sel_clauses                     true
% 3.04/0.98  --reset_solvers                         false
% 3.04/0.98  --bc_imp_inh                            [conj_cone]
% 3.04/0.98  --conj_cone_tolerance                   3.
% 3.04/0.98  --extra_neg_conj                        none
% 3.04/0.98  --large_theory_mode                     true
% 3.04/0.98  --prolific_symb_bound                   200
% 3.04/0.98  --lt_threshold                          2000
% 3.04/0.98  --clause_weak_htbl                      true
% 3.04/0.98  --gc_record_bc_elim                     false
% 3.04/0.98  
% 3.04/0.98  ------ Preprocessing Options
% 3.04/0.98  
% 3.04/0.98  --preprocessing_flag                    true
% 3.04/0.98  --time_out_prep_mult                    0.1
% 3.04/0.98  --splitting_mode                        input
% 3.04/0.98  --splitting_grd                         true
% 3.04/0.98  --splitting_cvd                         false
% 3.04/0.98  --splitting_cvd_svl                     false
% 3.04/0.98  --splitting_nvd                         32
% 3.04/0.98  --sub_typing                            true
% 3.04/0.98  --prep_gs_sim                           true
% 3.04/0.98  --prep_unflatten                        true
% 3.04/0.98  --prep_res_sim                          true
% 3.04/0.98  --prep_upred                            true
% 3.04/0.98  --prep_sem_filter                       exhaustive
% 3.04/0.98  --prep_sem_filter_out                   false
% 3.04/0.98  --pred_elim                             true
% 3.04/0.98  --res_sim_input                         true
% 3.04/0.98  --eq_ax_congr_red                       true
% 3.04/0.98  --pure_diseq_elim                       true
% 3.04/0.98  --brand_transform                       false
% 3.04/0.98  --non_eq_to_eq                          false
% 3.04/0.98  --prep_def_merge                        true
% 3.04/0.98  --prep_def_merge_prop_impl              false
% 3.04/0.98  --prep_def_merge_mbd                    true
% 3.04/0.98  --prep_def_merge_tr_red                 false
% 3.04/0.98  --prep_def_merge_tr_cl                  false
% 3.04/0.98  --smt_preprocessing                     true
% 3.04/0.98  --smt_ac_axioms                         fast
% 3.04/0.98  --preprocessed_out                      false
% 3.04/0.98  --preprocessed_stats                    false
% 3.04/0.98  
% 3.04/0.98  ------ Abstraction refinement Options
% 3.04/0.98  
% 3.04/0.98  --abstr_ref                             []
% 3.04/0.98  --abstr_ref_prep                        false
% 3.04/0.98  --abstr_ref_until_sat                   false
% 3.04/0.98  --abstr_ref_sig_restrict                funpre
% 3.04/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.04/0.98  --abstr_ref_under                       []
% 3.04/0.98  
% 3.04/0.98  ------ SAT Options
% 3.04/0.98  
% 3.04/0.98  --sat_mode                              false
% 3.04/0.98  --sat_fm_restart_options                ""
% 3.04/0.98  --sat_gr_def                            false
% 3.04/0.98  --sat_epr_types                         true
% 3.04/0.98  --sat_non_cyclic_types                  false
% 3.04/0.98  --sat_finite_models                     false
% 3.04/0.98  --sat_fm_lemmas                         false
% 3.04/0.98  --sat_fm_prep                           false
% 3.04/0.98  --sat_fm_uc_incr                        true
% 3.04/0.98  --sat_out_model                         small
% 3.04/0.98  --sat_out_clauses                       false
% 3.04/0.98  
% 3.04/0.98  ------ QBF Options
% 3.04/0.98  
% 3.04/0.98  --qbf_mode                              false
% 3.04/0.98  --qbf_elim_univ                         false
% 3.04/0.98  --qbf_dom_inst                          none
% 3.04/0.98  --qbf_dom_pre_inst                      false
% 3.04/0.98  --qbf_sk_in                             false
% 3.04/0.98  --qbf_pred_elim                         true
% 3.04/0.98  --qbf_split                             512
% 3.04/0.98  
% 3.04/0.98  ------ BMC1 Options
% 3.04/0.98  
% 3.04/0.98  --bmc1_incremental                      false
% 3.04/0.98  --bmc1_axioms                           reachable_all
% 3.04/0.98  --bmc1_min_bound                        0
% 3.04/0.98  --bmc1_max_bound                        -1
% 3.04/0.98  --bmc1_max_bound_default                -1
% 3.04/0.98  --bmc1_symbol_reachability              true
% 3.04/0.98  --bmc1_property_lemmas                  false
% 3.04/0.98  --bmc1_k_induction                      false
% 3.04/0.98  --bmc1_non_equiv_states                 false
% 3.04/0.98  --bmc1_deadlock                         false
% 3.04/0.98  --bmc1_ucm                              false
% 3.04/0.98  --bmc1_add_unsat_core                   none
% 3.04/0.98  --bmc1_unsat_core_children              false
% 3.04/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.04/0.98  --bmc1_out_stat                         full
% 3.04/0.98  --bmc1_ground_init                      false
% 3.04/0.98  --bmc1_pre_inst_next_state              false
% 3.04/0.98  --bmc1_pre_inst_state                   false
% 3.04/0.98  --bmc1_pre_inst_reach_state             false
% 3.04/0.98  --bmc1_out_unsat_core                   false
% 3.04/0.98  --bmc1_aig_witness_out                  false
% 3.04/0.98  --bmc1_verbose                          false
% 3.04/0.98  --bmc1_dump_clauses_tptp                false
% 3.04/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.04/0.98  --bmc1_dump_file                        -
% 3.04/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.04/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.04/0.98  --bmc1_ucm_extend_mode                  1
% 3.04/0.98  --bmc1_ucm_init_mode                    2
% 3.04/0.98  --bmc1_ucm_cone_mode                    none
% 3.04/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.04/0.98  --bmc1_ucm_relax_model                  4
% 3.04/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.04/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.04/0.98  --bmc1_ucm_layered_model                none
% 3.04/0.98  --bmc1_ucm_max_lemma_size               10
% 3.04/0.98  
% 3.04/0.98  ------ AIG Options
% 3.04/0.98  
% 3.04/0.98  --aig_mode                              false
% 3.04/0.98  
% 3.04/0.98  ------ Instantiation Options
% 3.04/0.98  
% 3.04/0.98  --instantiation_flag                    true
% 3.04/0.98  --inst_sos_flag                         false
% 3.04/0.98  --inst_sos_phase                        true
% 3.04/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.04/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.04/0.98  --inst_lit_sel_side                     none
% 3.04/0.98  --inst_solver_per_active                1400
% 3.04/0.98  --inst_solver_calls_frac                1.
% 3.04/0.98  --inst_passive_queue_type               priority_queues
% 3.04/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.04/0.98  --inst_passive_queues_freq              [25;2]
% 3.04/0.98  --inst_dismatching                      true
% 3.04/0.98  --inst_eager_unprocessed_to_passive     true
% 3.04/0.98  --inst_prop_sim_given                   true
% 3.04/0.98  --inst_prop_sim_new                     false
% 3.04/0.98  --inst_subs_new                         false
% 3.04/0.98  --inst_eq_res_simp                      false
% 3.04/0.98  --inst_subs_given                       false
% 3.04/0.98  --inst_orphan_elimination               true
% 3.04/0.98  --inst_learning_loop_flag               true
% 3.04/0.98  --inst_learning_start                   3000
% 3.04/0.98  --inst_learning_factor                  2
% 3.04/0.98  --inst_start_prop_sim_after_learn       3
% 3.04/0.98  --inst_sel_renew                        solver
% 3.04/0.98  --inst_lit_activity_flag                true
% 3.04/0.98  --inst_restr_to_given                   false
% 3.04/0.98  --inst_activity_threshold               500
% 3.04/0.98  --inst_out_proof                        true
% 3.04/0.98  
% 3.04/0.98  ------ Resolution Options
% 3.04/0.98  
% 3.04/0.98  --resolution_flag                       false
% 3.04/0.98  --res_lit_sel                           adaptive
% 3.04/0.98  --res_lit_sel_side                      none
% 3.04/0.98  --res_ordering                          kbo
% 3.04/0.98  --res_to_prop_solver                    active
% 3.04/0.98  --res_prop_simpl_new                    false
% 3.04/0.98  --res_prop_simpl_given                  true
% 3.04/0.98  --res_passive_queue_type                priority_queues
% 3.04/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.04/0.98  --res_passive_queues_freq               [15;5]
% 3.04/0.98  --res_forward_subs                      full
% 3.04/0.98  --res_backward_subs                     full
% 3.04/0.98  --res_forward_subs_resolution           true
% 3.04/0.98  --res_backward_subs_resolution          true
% 3.04/0.98  --res_orphan_elimination                true
% 3.04/0.98  --res_time_limit                        2.
% 3.04/0.98  --res_out_proof                         true
% 3.04/0.98  
% 3.04/0.98  ------ Superposition Options
% 3.04/0.98  
% 3.04/0.98  --superposition_flag                    true
% 3.04/0.98  --sup_passive_queue_type                priority_queues
% 3.04/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.04/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.04/0.98  --demod_completeness_check              fast
% 3.04/0.98  --demod_use_ground                      true
% 3.04/0.98  --sup_to_prop_solver                    passive
% 3.04/0.98  --sup_prop_simpl_new                    true
% 3.04/0.98  --sup_prop_simpl_given                  true
% 3.04/0.98  --sup_fun_splitting                     false
% 3.04/0.98  --sup_smt_interval                      50000
% 3.04/0.98  
% 3.04/0.98  ------ Superposition Simplification Setup
% 3.04/0.98  
% 3.04/0.98  --sup_indices_passive                   []
% 3.04/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.04/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.98  --sup_full_bw                           [BwDemod]
% 3.04/0.98  --sup_immed_triv                        [TrivRules]
% 3.04/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.04/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.98  --sup_immed_bw_main                     []
% 3.04/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.04/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.04/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.04/0.98  
% 3.04/0.98  ------ Combination Options
% 3.04/0.98  
% 3.04/0.98  --comb_res_mult                         3
% 3.04/0.98  --comb_sup_mult                         2
% 3.04/0.98  --comb_inst_mult                        10
% 3.04/0.98  
% 3.04/0.98  ------ Debug Options
% 3.04/0.98  
% 3.04/0.98  --dbg_backtrace                         false
% 3.04/0.98  --dbg_dump_prop_clauses                 false
% 3.04/0.98  --dbg_dump_prop_clauses_file            -
% 3.04/0.98  --dbg_out_stat                          false
% 3.04/0.98  
% 3.04/0.98  
% 3.04/0.98  
% 3.04/0.98  
% 3.04/0.98  ------ Proving...
% 3.04/0.98  
% 3.04/0.98  
% 3.04/0.98  % SZS status Theorem for theBenchmark.p
% 3.04/0.98  
% 3.04/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.04/0.98  
% 3.04/0.98  fof(f10,axiom,(
% 3.04/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.04/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/0.98  
% 3.04/0.98  fof(f24,plain,(
% 3.04/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.04/0.98    inference(ennf_transformation,[],[f10])).
% 3.04/0.98  
% 3.04/0.98  fof(f49,plain,(
% 3.04/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.04/0.98    inference(cnf_transformation,[],[f24])).
% 3.04/0.98  
% 3.04/0.98  fof(f13,conjecture,(
% 3.04/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 3.04/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/0.98  
% 3.04/0.98  fof(f14,negated_conjecture,(
% 3.04/0.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 3.04/0.98    inference(negated_conjecture,[],[f13])).
% 3.04/0.98  
% 3.04/0.98  fof(f28,plain,(
% 3.04/0.98    ? [X0,X1,X2] : ((k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 3.04/0.98    inference(ennf_transformation,[],[f14])).
% 3.04/0.98  
% 3.04/0.98  fof(f29,plain,(
% 3.04/0.98    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 3.04/0.98    inference(flattening,[],[f28])).
% 3.04/0.98  
% 3.04/0.98  fof(f35,plain,(
% 3.04/0.98    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_tarski(k1_funct_1(sK3,sK1)) != k2_relset_1(k1_tarski(sK1),sK2,sK3) & k1_xboole_0 != sK2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK3,k1_tarski(sK1),sK2) & v1_funct_1(sK3))),
% 3.04/0.98    introduced(choice_axiom,[])).
% 3.04/0.98  
% 3.04/0.98  fof(f36,plain,(
% 3.04/0.98    k1_tarski(k1_funct_1(sK3,sK1)) != k2_relset_1(k1_tarski(sK1),sK2,sK3) & k1_xboole_0 != sK2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK3,k1_tarski(sK1),sK2) & v1_funct_1(sK3)),
% 3.04/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f29,f35])).
% 3.04/0.98  
% 3.04/0.98  fof(f59,plain,(
% 3.04/0.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))),
% 3.04/0.98    inference(cnf_transformation,[],[f36])).
% 3.04/0.98  
% 3.04/0.98  fof(f2,axiom,(
% 3.04/0.98    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.04/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/0.98  
% 3.04/0.98  fof(f41,plain,(
% 3.04/0.98    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.04/0.98    inference(cnf_transformation,[],[f2])).
% 3.04/0.98  
% 3.04/0.98  fof(f3,axiom,(
% 3.04/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.04/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/0.98  
% 3.04/0.98  fof(f42,plain,(
% 3.04/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.04/0.98    inference(cnf_transformation,[],[f3])).
% 3.04/0.98  
% 3.04/0.98  fof(f62,plain,(
% 3.04/0.98    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 3.04/0.98    inference(definition_unfolding,[],[f41,f42])).
% 3.04/0.98  
% 3.04/0.98  fof(f70,plain,(
% 3.04/0.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)))),
% 3.04/0.98    inference(definition_unfolding,[],[f59,f62])).
% 3.04/0.98  
% 3.04/0.98  fof(f58,plain,(
% 3.04/0.98    v1_funct_2(sK3,k1_tarski(sK1),sK2)),
% 3.04/0.98    inference(cnf_transformation,[],[f36])).
% 3.04/0.98  
% 3.04/0.98  fof(f71,plain,(
% 3.04/0.98    v1_funct_2(sK3,k1_enumset1(sK1,sK1,sK1),sK2)),
% 3.04/0.98    inference(definition_unfolding,[],[f58,f62])).
% 3.04/0.98  
% 3.04/0.98  fof(f12,axiom,(
% 3.04/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.04/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/0.98  
% 3.04/0.98  fof(f26,plain,(
% 3.04/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.04/0.98    inference(ennf_transformation,[],[f12])).
% 3.04/0.98  
% 3.04/0.98  fof(f27,plain,(
% 3.04/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.04/0.98    inference(flattening,[],[f26])).
% 3.04/0.98  
% 3.04/0.98  fof(f34,plain,(
% 3.04/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.04/0.98    inference(nnf_transformation,[],[f27])).
% 3.04/0.98  
% 3.04/0.98  fof(f51,plain,(
% 3.04/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.04/0.98    inference(cnf_transformation,[],[f34])).
% 3.04/0.98  
% 3.04/0.98  fof(f60,plain,(
% 3.04/0.98    k1_xboole_0 != sK2),
% 3.04/0.98    inference(cnf_transformation,[],[f36])).
% 3.04/0.98  
% 3.04/0.98  fof(f1,axiom,(
% 3.04/0.98    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.04/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/0.98  
% 3.04/0.98  fof(f30,plain,(
% 3.04/0.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.04/0.98    inference(nnf_transformation,[],[f1])).
% 3.04/0.98  
% 3.04/0.98  fof(f31,plain,(
% 3.04/0.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.04/0.98    inference(rectify,[],[f30])).
% 3.04/0.98  
% 3.04/0.98  fof(f32,plain,(
% 3.04/0.98    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1))))),
% 3.04/0.98    introduced(choice_axiom,[])).
% 3.04/0.98  
% 3.04/0.98  fof(f33,plain,(
% 3.04/0.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.04/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).
% 3.04/0.98  
% 3.04/0.98  fof(f38,plain,(
% 3.04/0.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 3.04/0.98    inference(cnf_transformation,[],[f33])).
% 3.04/0.98  
% 3.04/0.98  fof(f65,plain,(
% 3.04/0.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_enumset1(X0,X0,X0) != X1) )),
% 3.04/0.98    inference(definition_unfolding,[],[f38,f62])).
% 3.04/0.98  
% 3.04/0.98  fof(f72,plain,(
% 3.04/0.98    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_enumset1(X3,X3,X3) != X1) )),
% 3.04/0.98    inference(equality_resolution,[],[f65])).
% 3.04/0.98  
% 3.04/0.98  fof(f73,plain,(
% 3.04/0.98    ( ! [X3] : (r2_hidden(X3,k1_enumset1(X3,X3,X3))) )),
% 3.04/0.98    inference(equality_resolution,[],[f72])).
% 3.04/0.98  
% 3.04/0.98  fof(f8,axiom,(
% 3.04/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.04/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/0.98  
% 3.04/0.98  fof(f22,plain,(
% 3.04/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.04/0.98    inference(ennf_transformation,[],[f8])).
% 3.04/0.98  
% 3.04/0.98  fof(f47,plain,(
% 3.04/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.04/0.98    inference(cnf_transformation,[],[f22])).
% 3.04/0.98  
% 3.04/0.98  fof(f7,axiom,(
% 3.04/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)))),
% 3.04/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/0.98  
% 3.04/0.98  fof(f20,plain,(
% 3.04/0.98    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.04/0.98    inference(ennf_transformation,[],[f7])).
% 3.04/0.98  
% 3.04/0.98  fof(f21,plain,(
% 3.04/0.98    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.04/0.98    inference(flattening,[],[f20])).
% 3.04/0.98  
% 3.04/0.98  fof(f46,plain,(
% 3.04/0.98    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.04/0.98    inference(cnf_transformation,[],[f21])).
% 3.04/0.98  
% 3.04/0.98  fof(f68,plain,(
% 3.04/0.98    ( ! [X0,X1] : (k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.04/0.98    inference(definition_unfolding,[],[f46,f62])).
% 3.04/0.98  
% 3.04/0.98  fof(f57,plain,(
% 3.04/0.98    v1_funct_1(sK3)),
% 3.04/0.98    inference(cnf_transformation,[],[f36])).
% 3.04/0.98  
% 3.04/0.98  fof(f4,axiom,(
% 3.04/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 3.04/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/0.98  
% 3.04/0.98  fof(f16,plain,(
% 3.04/0.98    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 3.04/0.98    inference(ennf_transformation,[],[f4])).
% 3.04/0.98  
% 3.04/0.98  fof(f43,plain,(
% 3.04/0.98    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 3.04/0.98    inference(cnf_transformation,[],[f16])).
% 3.04/0.98  
% 3.04/0.98  fof(f67,plain,(
% 3.04/0.98    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_enumset1(X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 3.04/0.98    inference(definition_unfolding,[],[f43,f62])).
% 3.04/0.98  
% 3.04/0.98  fof(f11,axiom,(
% 3.04/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.04/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/0.98  
% 3.04/0.98  fof(f25,plain,(
% 3.04/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.04/0.98    inference(ennf_transformation,[],[f11])).
% 3.04/0.98  
% 3.04/0.98  fof(f50,plain,(
% 3.04/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.04/0.98    inference(cnf_transformation,[],[f25])).
% 3.04/0.98  
% 3.04/0.98  fof(f61,plain,(
% 3.04/0.98    k1_tarski(k1_funct_1(sK3,sK1)) != k2_relset_1(k1_tarski(sK1),sK2,sK3)),
% 3.04/0.98    inference(cnf_transformation,[],[f36])).
% 3.04/0.98  
% 3.04/0.98  fof(f69,plain,(
% 3.04/0.98    k1_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK3)),
% 3.04/0.98    inference(definition_unfolding,[],[f61,f62,f62])).
% 3.04/0.98  
% 3.04/0.98  fof(f9,axiom,(
% 3.04/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.04/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f15,plain,(
% 3.04/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.04/0.99    inference(pure_predicate_removal,[],[f9])).
% 3.04/0.99  
% 3.04/0.99  fof(f23,plain,(
% 3.04/0.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.04/0.99    inference(ennf_transformation,[],[f15])).
% 3.04/0.99  
% 3.04/0.99  fof(f48,plain,(
% 3.04/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.04/0.99    inference(cnf_transformation,[],[f23])).
% 3.04/0.99  
% 3.04/0.99  fof(f6,axiom,(
% 3.04/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 3.04/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f18,plain,(
% 3.04/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.04/0.99    inference(ennf_transformation,[],[f6])).
% 3.04/0.99  
% 3.04/0.99  fof(f19,plain,(
% 3.04/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.04/0.99    inference(flattening,[],[f18])).
% 3.04/0.99  
% 3.04/0.99  fof(f45,plain,(
% 3.04/0.99    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f19])).
% 3.04/0.99  
% 3.04/0.99  fof(f5,axiom,(
% 3.04/0.99    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 3.04/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f17,plain,(
% 3.04/0.99    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 3.04/0.99    inference(ennf_transformation,[],[f5])).
% 3.04/0.99  
% 3.04/0.99  fof(f44,plain,(
% 3.04/0.99    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f17])).
% 3.04/0.99  
% 3.04/0.99  cnf(c_10,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.04/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_20,negated_conjecture,
% 3.04/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))) ),
% 3.04/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_468,plain,
% 3.04/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.04/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.04/0.99      | sK3 != X2 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_20]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_469,plain,
% 3.04/0.99      ( k1_relset_1(X0,X1,sK3) = k1_relat_1(sK3)
% 3.04/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_468]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1290,plain,
% 3.04/0.99      ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK3) = k1_relat_1(sK3) ),
% 3.04/0.99      inference(equality_resolution,[status(thm)],[c_469]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_21,negated_conjecture,
% 3.04/0.99      ( v1_funct_2(sK3,k1_enumset1(sK1,sK1,sK1),sK2) ),
% 3.04/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_17,plain,
% 3.04/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.04/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.04/0.99      | k1_xboole_0 = X2 ),
% 3.04/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_423,plain,
% 3.04/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.04/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.04/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 3.04/0.99      | sK3 != X0
% 3.04/0.99      | k1_xboole_0 = X2 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_20]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_424,plain,
% 3.04/0.99      ( ~ v1_funct_2(sK3,X0,X1)
% 3.04/0.99      | k1_relset_1(X0,X1,sK3) = X0
% 3.04/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.04/0.99      | k1_xboole_0 = X1 ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_423]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_712,plain,
% 3.04/0.99      ( k1_relset_1(X0,X1,sK3) = X0
% 3.04/0.99      | k1_enumset1(sK1,sK1,sK1) != X0
% 3.04/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.04/0.99      | sK2 != X1
% 3.04/0.99      | sK3 != sK3
% 3.04/0.99      | k1_xboole_0 = X1 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_424]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_713,plain,
% 3.04/0.99      ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK3) = k1_enumset1(sK1,sK1,sK1)
% 3.04/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))
% 3.04/0.99      | k1_xboole_0 = sK2 ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_712]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_19,negated_conjecture,
% 3.04/0.99      ( k1_xboole_0 != sK2 ),
% 3.04/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_714,plain,
% 3.04/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))
% 3.04/0.99      | k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK3) = k1_enumset1(sK1,sK1,sK1) ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_713,c_19]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_715,plain,
% 3.04/0.99      ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK3) = k1_enumset1(sK1,sK1,sK1)
% 3.04/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
% 3.04/0.99      inference(renaming,[status(thm)],[c_714]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_769,plain,
% 3.04/0.99      ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK3) = k1_enumset1(sK1,sK1,sK1) ),
% 3.04/0.99      inference(equality_resolution_simp,[status(thm)],[c_715]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1484,plain,
% 3.04/0.99      ( k1_enumset1(sK1,sK1,sK1) = k1_relat_1(sK3) ),
% 3.04/0.99      inference(demodulation,[status(thm)],[c_1290,c_769]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2,plain,
% 3.04/0.99      ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) ),
% 3.04/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1123,plain,
% 3.04/0.99      ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) = iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1554,plain,
% 3.04/0.99      ( r2_hidden(sK1,k1_relat_1(sK3)) = iProver_top ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_1484,c_1123]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_8,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/0.99      | v1_relat_1(X0) ),
% 3.04/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_477,plain,
% 3.04/0.99      ( v1_relat_1(X0)
% 3.04/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 3.04/0.99      | sK3 != X0 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_20]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_478,plain,
% 3.04/0.99      ( v1_relat_1(sK3)
% 3.04/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_477]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_7,plain,
% 3.04/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.04/0.99      | ~ v1_funct_1(X1)
% 3.04/0.99      | ~ v1_relat_1(X1)
% 3.04/0.99      | k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ),
% 3.04/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_22,negated_conjecture,
% 3.04/0.99      ( v1_funct_1(sK3) ),
% 3.04/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_269,plain,
% 3.04/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.04/0.99      | ~ v1_relat_1(X1)
% 3.04/0.99      | k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
% 3.04/0.99      | sK3 != X1 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_22]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_270,plain,
% 3.04/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 3.04/0.99      | ~ v1_relat_1(sK3)
% 3.04/0.99      | k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0) ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_269]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_591,plain,
% 3.04/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 3.04/0.99      | k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
% 3.04/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
% 3.04/0.99      inference(resolution,[status(thm)],[c_478,c_270]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_887,plain,
% 3.04/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 3.04/0.99      | k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
% 3.04/0.99      | ~ sP3_iProver_split ),
% 3.04/0.99      inference(splitting,
% 3.04/0.99                [splitting(split),new_symbols(definition,[sP3_iProver_split])],
% 3.04/0.99                [c_591]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1120,plain,
% 3.04/0.99      ( k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
% 3.04/0.99      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 3.04/0.99      | sP3_iProver_split != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_887]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_888,plain,
% 3.04/0.99      ( sP3_iProver_split | sP0_iProver_split ),
% 3.04/0.99      inference(splitting,
% 3.04/0.99                [splitting(split),new_symbols(definition,[])],
% 3.04/0.99                [c_591]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_930,plain,
% 3.04/0.99      ( sP3_iProver_split = iProver_top
% 3.04/0.99      | sP0_iProver_split = iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_888]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_931,plain,
% 3.04/0.99      ( k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
% 3.04/0.99      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 3.04/0.99      | sP3_iProver_split != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_887]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_890,plain,( X0 = X0 ),theory(equality) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1231,plain,
% 3.04/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) = k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_890]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4,plain,
% 3.04/0.99      ( ~ v1_relat_1(X0)
% 3.04/0.99      | k9_relat_1(X0,k1_enumset1(X1,X1,X1)) = k11_relat_1(X0,X1) ),
% 3.04/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_614,plain,
% 3.04/0.99      ( k9_relat_1(X0,k1_enumset1(X1,X1,X1)) = k11_relat_1(X0,X1)
% 3.04/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
% 3.04/0.99      | sK3 != X0 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_478]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_615,plain,
% 3.04/0.99      ( k9_relat_1(sK3,k1_enumset1(X0,X0,X0)) = k11_relat_1(sK3,X0)
% 3.04/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_614]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_882,plain,
% 3.04/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.04/0.99      | ~ sP0_iProver_split ),
% 3.04/0.99      inference(splitting,
% 3.04/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.04/0.99                [c_615]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1232,plain,
% 3.04/0.99      ( ~ sP0_iProver_split
% 3.04/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_882]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1236,plain,
% 3.04/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))
% 3.04/0.99      | sP0_iProver_split != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_1232]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2353,plain,
% 3.04/0.99      ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 3.04/0.99      | k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0) ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_1120,c_930,c_931,c_1231,c_1236]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2354,plain,
% 3.04/0.99      ( k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
% 3.04/0.99      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top ),
% 3.04/0.99      inference(renaming,[status(thm)],[c_2353]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2362,plain,
% 3.04/0.99      ( k1_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) = k11_relat_1(sK3,sK1) ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_1554,c_2354]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_11,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.04/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_459,plain,
% 3.04/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.04/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.04/0.99      | sK3 != X2 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_20]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_460,plain,
% 3.04/0.99      ( k2_relset_1(X0,X1,sK3) = k2_relat_1(sK3)
% 3.04/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_459]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1245,plain,
% 3.04/0.99      ( k2_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK3) = k2_relat_1(sK3) ),
% 3.04/0.99      inference(equality_resolution,[status(thm)],[c_460]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_18,negated_conjecture,
% 3.04/0.99      ( k1_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK3) ),
% 3.04/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1444,plain,
% 3.04/0.99      ( k1_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relat_1(sK3) ),
% 3.04/0.99      inference(demodulation,[status(thm)],[c_1245,c_18]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_11695,plain,
% 3.04/0.99      ( k11_relat_1(sK3,sK1) != k2_relat_1(sK3) ),
% 3.04/0.99      inference(demodulation,[status(thm)],[c_2362,c_1444]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_9,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/0.99      | v4_relat_1(X0,X1) ),
% 3.04/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_6,plain,
% 3.04/0.99      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 3.04/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_249,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/0.99      | ~ v1_relat_1(X0)
% 3.04/0.99      | k7_relat_1(X0,X1) = X0 ),
% 3.04/0.99      inference(resolution,[status(thm)],[c_9,c_6]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_253,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/0.99      | k7_relat_1(X0,X1) = X0 ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_249,c_9,c_8,c_6]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_414,plain,
% 3.04/0.99      ( k7_relat_1(X0,X1) = X0
% 3.04/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 3.04/0.99      | sK3 != X0 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_253,c_20]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_415,plain,
% 3.04/0.99      ( k7_relat_1(sK3,X0) = sK3
% 3.04/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_414]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1242,plain,
% 3.04/0.99      ( k7_relat_1(sK3,k1_enumset1(sK1,sK1,sK1)) = sK3 ),
% 3.04/0.99      inference(equality_resolution,[status(thm)],[c_415]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1522,plain,
% 3.04/0.99      ( k7_relat_1(sK3,k1_relat_1(sK3)) = sK3 ),
% 3.04/0.99      inference(demodulation,[status(thm)],[c_1484,c_1242]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_5,plain,
% 3.04/0.99      ( ~ v1_relat_1(X0)
% 3.04/0.99      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 3.04/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_605,plain,
% 3.04/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.04/0.99      | k2_relat_1(k7_relat_1(X2,X3)) = k9_relat_1(X2,X3)
% 3.04/0.99      | sK3 != X2 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_478]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_606,plain,
% 3.04/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.04/0.99      | k2_relat_1(k7_relat_1(sK3,X2)) = k9_relat_1(sK3,X2) ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_605]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_885,plain,
% 3.04/0.99      ( k2_relat_1(k7_relat_1(sK3,X0)) = k9_relat_1(sK3,X0)
% 3.04/0.99      | ~ sP2_iProver_split ),
% 3.04/0.99      inference(splitting,
% 3.04/0.99                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 3.04/0.99                [c_606]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1118,plain,
% 3.04/0.99      ( k2_relat_1(k7_relat_1(sK3,X0)) = k9_relat_1(sK3,X0)
% 3.04/0.99      | sP2_iProver_split != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_885]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_886,plain,
% 3.04/0.99      ( sP2_iProver_split | sP0_iProver_split ),
% 3.04/0.99      inference(splitting,
% 3.04/0.99                [splitting(split),new_symbols(definition,[])],
% 3.04/0.99                [c_606]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2254,plain,
% 3.04/0.99      ( k2_relat_1(k7_relat_1(sK3,X0)) = k9_relat_1(sK3,X0) ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_1118,c_886,c_885,c_1231,c_1232]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2258,plain,
% 3.04/0.99      ( k9_relat_1(sK3,k1_relat_1(sK3)) = k2_relat_1(sK3) ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_1522,c_2254]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_883,plain,
% 3.04/0.99      ( k9_relat_1(sK3,k1_enumset1(X0,X0,X0)) = k11_relat_1(sK3,X0)
% 3.04/0.99      | ~ sP1_iProver_split ),
% 3.04/0.99      inference(splitting,
% 3.04/0.99                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 3.04/0.99                [c_615]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1114,plain,
% 3.04/0.99      ( k9_relat_1(sK3,k1_enumset1(X0,X0,X0)) = k11_relat_1(sK3,X0)
% 3.04/0.99      | sP1_iProver_split != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_883]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_884,plain,
% 3.04/0.99      ( sP1_iProver_split | sP0_iProver_split ),
% 3.04/0.99      inference(splitting,
% 3.04/0.99                [splitting(split),new_symbols(definition,[])],
% 3.04/0.99                [c_615]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1849,plain,
% 3.04/0.99      ( k9_relat_1(sK3,k1_enumset1(X0,X0,X0)) = k11_relat_1(sK3,X0) ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_1114,c_884,c_883,c_1231,c_1232]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1853,plain,
% 3.04/0.99      ( k9_relat_1(sK3,k1_relat_1(sK3)) = k11_relat_1(sK3,sK1) ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_1484,c_1849]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_9616,plain,
% 3.04/0.99      ( k11_relat_1(sK3,sK1) = k2_relat_1(sK3) ),
% 3.04/0.99      inference(demodulation,[status(thm)],[c_2258,c_1853]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(contradiction,plain,
% 3.04/0.99      ( $false ),
% 3.04/0.99      inference(minisat,[status(thm)],[c_11695,c_9616]) ).
% 3.04/0.99  
% 3.04/0.99  
% 3.04/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.04/0.99  
% 3.04/0.99  ------                               Statistics
% 3.04/0.99  
% 3.04/0.99  ------ General
% 3.04/0.99  
% 3.04/0.99  abstr_ref_over_cycles:                  0
% 3.04/0.99  abstr_ref_under_cycles:                 0
% 3.04/0.99  gc_basic_clause_elim:                   0
% 3.04/0.99  forced_gc_time:                         0
% 3.04/0.99  parsing_time:                           0.013
% 3.04/0.99  unif_index_cands_time:                  0.
% 3.04/0.99  unif_index_add_time:                    0.
% 3.04/0.99  orderings_time:                         0.
% 3.04/0.99  out_proof_time:                         0.012
% 3.04/0.99  total_time:                             0.371
% 3.04/0.99  num_of_symbols:                         57
% 3.04/0.99  num_of_terms:                           7583
% 3.04/0.99  
% 3.04/0.99  ------ Preprocessing
% 3.04/0.99  
% 3.04/0.99  num_of_splits:                          6
% 3.04/0.99  num_of_split_atoms:                     4
% 3.04/0.99  num_of_reused_defs:                     2
% 3.04/0.99  num_eq_ax_congr_red:                    21
% 3.04/0.99  num_of_sem_filtered_clauses:            1
% 3.04/0.99  num_of_subtypes:                        0
% 3.04/0.99  monotx_restored_types:                  0
% 3.04/0.99  sat_num_of_epr_types:                   0
% 3.04/0.99  sat_num_of_non_cyclic_types:            0
% 3.04/0.99  sat_guarded_non_collapsed_types:        0
% 3.04/0.99  num_pure_diseq_elim:                    0
% 3.04/0.99  simp_replaced_by:                       0
% 3.04/0.99  res_preprocessed:                       105
% 3.04/0.99  prep_upred:                             0
% 3.04/0.99  prep_unflattend:                        51
% 3.04/0.99  smt_new_axioms:                         0
% 3.04/0.99  pred_elim_cands:                        1
% 3.04/0.99  pred_elim:                              5
% 3.04/0.99  pred_elim_cl:                           8
% 3.04/0.99  pred_elim_cycles:                       10
% 3.04/0.99  merged_defs:                            0
% 3.04/0.99  merged_defs_ncl:                        0
% 3.04/0.99  bin_hyper_res:                          0
% 3.04/0.99  prep_cycles:                            4
% 3.04/0.99  pred_elim_time:                         0.012
% 3.04/0.99  splitting_time:                         0.
% 3.04/0.99  sem_filter_time:                        0.
% 3.04/0.99  monotx_time:                            0.
% 3.04/0.99  subtype_inf_time:                       0.
% 3.04/0.99  
% 3.04/0.99  ------ Problem properties
% 3.04/0.99  
% 3.04/0.99  clauses:                                21
% 3.04/0.99  conjectures:                            2
% 3.04/0.99  epr:                                    4
% 3.04/0.99  horn:                                   16
% 3.04/0.99  ground:                                 8
% 3.04/0.99  unary:                                  4
% 3.04/0.99  binary:                                 12
% 3.04/0.99  lits:                                   44
% 3.04/0.99  lits_eq:                                27
% 3.04/0.99  fd_pure:                                0
% 3.04/0.99  fd_pseudo:                              0
% 3.04/0.99  fd_cond:                                0
% 3.04/0.99  fd_pseudo_cond:                         2
% 3.04/0.99  ac_symbols:                             0
% 3.04/0.99  
% 3.04/0.99  ------ Propositional Solver
% 3.04/0.99  
% 3.04/0.99  prop_solver_calls:                      29
% 3.04/0.99  prop_fast_solver_calls:                 928
% 3.04/0.99  smt_solver_calls:                       0
% 3.04/0.99  smt_fast_solver_calls:                  0
% 3.04/0.99  prop_num_of_clauses:                    3199
% 3.04/0.99  prop_preprocess_simplified:             6613
% 3.04/0.99  prop_fo_subsumed:                       14
% 3.04/0.99  prop_solver_time:                       0.
% 3.04/0.99  smt_solver_time:                        0.
% 3.04/0.99  smt_fast_solver_time:                   0.
% 3.04/0.99  prop_fast_solver_time:                  0.
% 3.04/0.99  prop_unsat_core_time:                   0.
% 3.04/0.99  
% 3.04/0.99  ------ QBF
% 3.04/0.99  
% 3.04/0.99  qbf_q_res:                              0
% 3.04/0.99  qbf_num_tautologies:                    0
% 3.04/0.99  qbf_prep_cycles:                        0
% 3.04/0.99  
% 3.04/0.99  ------ BMC1
% 3.04/0.99  
% 3.04/0.99  bmc1_current_bound:                     -1
% 3.04/0.99  bmc1_last_solved_bound:                 -1
% 3.04/0.99  bmc1_unsat_core_size:                   -1
% 3.04/0.99  bmc1_unsat_core_parents_size:           -1
% 3.04/0.99  bmc1_merge_next_fun:                    0
% 3.04/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.04/0.99  
% 3.04/0.99  ------ Instantiation
% 3.04/0.99  
% 3.04/0.99  inst_num_of_clauses:                    1024
% 3.04/0.99  inst_num_in_passive:                    240
% 3.04/0.99  inst_num_in_active:                     372
% 3.04/0.99  inst_num_in_unprocessed:                412
% 3.04/0.99  inst_num_of_loops:                      430
% 3.04/0.99  inst_num_of_learning_restarts:          0
% 3.04/0.99  inst_num_moves_active_passive:          55
% 3.04/0.99  inst_lit_activity:                      0
% 3.04/0.99  inst_lit_activity_moves:                0
% 3.04/0.99  inst_num_tautologies:                   0
% 3.04/0.99  inst_num_prop_implied:                  0
% 3.04/0.99  inst_num_existing_simplified:           0
% 3.04/0.99  inst_num_eq_res_simplified:             0
% 3.04/0.99  inst_num_child_elim:                    0
% 3.04/0.99  inst_num_of_dismatching_blockings:      588
% 3.04/0.99  inst_num_of_non_proper_insts:           1190
% 3.04/0.99  inst_num_of_duplicates:                 0
% 3.04/0.99  inst_inst_num_from_inst_to_res:         0
% 3.04/0.99  inst_dismatching_checking_time:         0.
% 3.04/0.99  
% 3.04/0.99  ------ Resolution
% 3.04/0.99  
% 3.04/0.99  res_num_of_clauses:                     0
% 3.04/0.99  res_num_in_passive:                     0
% 3.04/0.99  res_num_in_active:                      0
% 3.04/0.99  res_num_of_loops:                       109
% 3.04/0.99  res_forward_subset_subsumed:            138
% 3.04/0.99  res_backward_subset_subsumed:           0
% 3.04/0.99  res_forward_subsumed:                   0
% 3.04/0.99  res_backward_subsumed:                  0
% 3.04/0.99  res_forward_subsumption_resolution:     0
% 3.04/0.99  res_backward_subsumption_resolution:    0
% 3.04/0.99  res_clause_to_clause_subsumption:       2754
% 3.04/0.99  res_orphan_elimination:                 0
% 3.04/0.99  res_tautology_del:                      61
% 3.04/0.99  res_num_eq_res_simplified:              1
% 3.04/0.99  res_num_sel_changes:                    0
% 3.04/0.99  res_moves_from_active_to_pass:          0
% 3.04/0.99  
% 3.04/0.99  ------ Superposition
% 3.04/0.99  
% 3.04/0.99  sup_time_total:                         0.
% 3.04/0.99  sup_time_generating:                    0.
% 3.04/0.99  sup_time_sim_full:                      0.
% 3.04/0.99  sup_time_sim_immed:                     0.
% 3.04/0.99  
% 3.04/0.99  sup_num_of_clauses:                     316
% 3.04/0.99  sup_num_in_active:                      65
% 3.04/0.99  sup_num_in_passive:                     251
% 3.04/0.99  sup_num_of_loops:                       85
% 3.04/0.99  sup_fw_superposition:                   297
% 3.04/0.99  sup_bw_superposition:                   174
% 3.04/0.99  sup_immediate_simplified:               113
% 3.04/0.99  sup_given_eliminated:                   0
% 3.04/0.99  comparisons_done:                       0
% 3.04/0.99  comparisons_avoided:                    60
% 3.04/0.99  
% 3.04/0.99  ------ Simplifications
% 3.04/0.99  
% 3.04/0.99  
% 3.04/0.99  sim_fw_subset_subsumed:                 25
% 3.04/0.99  sim_bw_subset_subsumed:                 2
% 3.04/0.99  sim_fw_subsumed:                        74
% 3.04/0.99  sim_bw_subsumed:                        2
% 3.04/0.99  sim_fw_subsumption_res:                 2
% 3.04/0.99  sim_bw_subsumption_res:                 0
% 3.04/0.99  sim_tautology_del:                      3
% 3.04/0.99  sim_eq_tautology_del:                   3
% 3.04/0.99  sim_eq_res_simp:                        2
% 3.04/0.99  sim_fw_demodulated:                     6
% 3.04/0.99  sim_bw_demodulated:                     20
% 3.04/0.99  sim_light_normalised:                   16
% 3.04/0.99  sim_joinable_taut:                      0
% 3.04/0.99  sim_joinable_simp:                      0
% 3.04/0.99  sim_ac_normalised:                      0
% 3.04/0.99  sim_smt_subsumption:                    0
% 3.04/0.99  
%------------------------------------------------------------------------------
