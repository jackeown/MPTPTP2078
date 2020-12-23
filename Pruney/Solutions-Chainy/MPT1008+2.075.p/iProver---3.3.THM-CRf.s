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
% DateTime   : Thu Dec  3 12:05:19 EST 2020

% Result     : Theorem 7.52s
% Output     : CNFRefutation 7.52s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 947 expanded)
%              Number of clauses        :   80 ( 237 expanded)
%              Number of leaves         :   18 ( 226 expanded)
%              Depth                    :   24
%              Number of atoms          :  400 (2450 expanded)
%              Number of equality atoms :  217 (1204 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k1_relat_1(X1))
          | k1_xboole_0 = k11_relat_1(X1,X0) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X1))
      | k1_xboole_0 = k11_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

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

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f36,plain,
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

fof(f37,plain,
    ( k1_tarski(k1_funct_1(sK3,sK1)) != k2_relset_1(k1_tarski(sK1),sK2,sK3)
    & k1_xboole_0 != sK2
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
    & v1_funct_2(sK3,k1_tarski(sK1),sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f29,f36])).

fof(f61,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) ),
    inference(cnf_transformation,[],[f37])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f46,f47])).

fof(f65,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f45,f64])).

fof(f75,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
    inference(definition_unfolding,[],[f61,f65])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f51,f65])).

fof(f59,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f63,plain,(
    k1_tarski(k1_funct_1(sK3,sK1)) != k2_relset_1(k1_tarski(sK1),sK2,sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f74,plain,(
    k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) ),
    inference(definition_unfolding,[],[f63,f65,f65])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f48,f65])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
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

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f33,plain,(
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

fof(f34,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f69,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f41,f64])).

fof(f77,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f69])).

fof(f78,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_enumset1(X0,X0,X0,X4)) ),
    inference(equality_resolution,[],[f77])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f26])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f60,plain,(
    v1_funct_2(sK3,k1_tarski(sK1),sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f76,plain,(
    v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
    inference(definition_unfolding,[],[f60,f65])).

fof(f62,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_244,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_11])).

cnf(c_245,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_244])).

cnf(c_14885,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,X0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_245])).

cnf(c_14887,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK1),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_14885])).

cnf(c_8,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k11_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_331,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_20])).

cnf(c_332,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_331])).

cnf(c_392,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | k11_relat_1(X1,X0) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_332])).

cnf(c_393,plain,
    ( r2_hidden(X0,k1_relat_1(sK3))
    | k11_relat_1(sK3,X0) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
    inference(unflattening,[status(thm)],[c_392])).

cnf(c_505,plain,
    ( r2_hidden(X0,k1_relat_1(sK3))
    | k11_relat_1(sK3,X0) = k1_xboole_0
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_393])).

cnf(c_821,plain,
    ( k11_relat_1(sK3,X0) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK3)) = iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_505])).

cnf(c_506,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_393])).

cnf(c_544,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_506])).

cnf(c_545,plain,
    ( k11_relat_1(sK3,X0) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK3)) = iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_505])).

cnf(c_504,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_393])).

cnf(c_912,plain,
    ( ~ sP0_iProver_split
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_504])).

cnf(c_913,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_912])).

cnf(c_514,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_963,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) = k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_514])).

cnf(c_1133,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) = iProver_top
    | k11_relat_1(sK3,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_821,c_544,c_545,c_913,c_963])).

cnf(c_1134,plain,
    ( k11_relat_1(sK3,X0) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_1133])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_276,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_22])).

cnf(c_277,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_276])).

cnf(c_354,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
    inference(resolution,[status(thm)],[c_332,c_277])).

cnf(c_511,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
    | ~ sP4_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP4_iProver_split])],[c_354])).

cnf(c_830,plain,
    ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | sP4_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_511])).

cnf(c_512,plain,
    ( sP4_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_354])).

cnf(c_561,plain,
    ( sP4_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_512])).

cnf(c_562,plain,
    ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | sP4_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_511])).

cnf(c_1623,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_830,c_561,c_562,c_913,c_963])).

cnf(c_1624,plain,
    ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1623])).

cnf(c_1629,plain,
    ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
    | k11_relat_1(sK3,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1134,c_1624])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_322,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_20])).

cnf(c_323,plain,
    ( k2_relset_1(X0,X1,sK3) = k2_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_322])).

cnf(c_930,plain,
    ( k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) = k2_relat_1(sK3) ),
    inference(equality_resolution,[status(thm)],[c_323])).

cnf(c_18,negated_conjecture,
    ( k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1085,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_930,c_18])).

cnf(c_2019,plain,
    ( k11_relat_1(sK3,sK1) != k2_relat_1(sK3)
    | k11_relat_1(sK3,sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1629,c_1085])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_368,plain,
    ( k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_332])).

cnf(c_369,plain,
    ( k9_relat_1(sK3,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK3,X0)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
    inference(unflattening,[status(thm)],[c_368])).

cnf(c_509,plain,
    ( k9_relat_1(sK3,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK3,X0)
    | ~ sP3_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP3_iProver_split])],[c_369])).

cnf(c_827,plain,
    ( k9_relat_1(sK3,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK3,X0)
    | sP3_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_509])).

cnf(c_510,plain,
    ( sP3_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_369])).

cnf(c_1437,plain,
    ( k9_relat_1(sK3,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_827,c_510,c_509,c_912,c_963])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_313,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_20])).

cnf(c_314,plain,
    ( k7_relset_1(X0,X1,sK3,X2) = k9_relat_1(sK3,X2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_313])).

cnf(c_931,plain,
    ( k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(equality_resolution,[status(thm)],[c_314])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_295,plain,
    ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_20])).

cnf(c_296,plain,
    ( k7_relset_1(X0,X1,sK3,X0) = k2_relset_1(X0,X1,sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_295])).

cnf(c_988,plain,
    ( k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3,k2_enumset1(sK1,sK1,sK1,sK1)) = k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) ),
    inference(equality_resolution,[status(thm)],[c_296])).

cnf(c_989,plain,
    ( k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3,k2_enumset1(sK1,sK1,sK1,sK1)) = k2_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_988,c_930])).

cnf(c_1440,plain,
    ( k9_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1)) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_931,c_989])).

cnf(c_1499,plain,
    ( k11_relat_1(sK3,sK1) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1437,c_1440])).

cnf(c_2021,plain,
    ( k11_relat_1(sK3,sK1) = k1_xboole_0
    | k2_relat_1(sK3) != k2_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_2019,c_1499])).

cnf(c_2022,plain,
    ( k11_relat_1(sK3,sK1) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_2021])).

cnf(c_2216,plain,
    ( k2_relat_1(sK3) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2022,c_1499])).

cnf(c_4,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_836,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_21,negated_conjecture,
    ( v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_255,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | k2_enumset1(sK1,sK1,sK1,sK1) != X1
    | sK2 != X2
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_21])).

cnf(c_256,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))
    | ~ r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1))
    | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3))
    | ~ v1_funct_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_255])).

cnf(c_19,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_260,plain,
    ( ~ r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1))
    | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_256,c_22,c_20,c_19])).

cnf(c_832,plain,
    ( r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_260])).

cnf(c_1321,plain,
    ( r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_832,c_930])).

cnf(c_1325,plain,
    ( r2_hidden(k1_funct_1(sK3,sK1),k2_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_836,c_1321])).

cnf(c_7476,plain,
    ( r2_hidden(k1_funct_1(sK3,sK1),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2216,c_1325])).

cnf(c_7483,plain,
    ( r2_hidden(k1_funct_1(sK3,sK1),k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7476])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14887,c_7483])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:19:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.52/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.52/1.49  
% 7.52/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.52/1.49  
% 7.52/1.49  ------  iProver source info
% 7.52/1.49  
% 7.52/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.52/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.52/1.49  git: non_committed_changes: false
% 7.52/1.49  git: last_make_outside_of_git: false
% 7.52/1.49  
% 7.52/1.49  ------ 
% 7.52/1.49  
% 7.52/1.49  ------ Input Options
% 7.52/1.49  
% 7.52/1.49  --out_options                           all
% 7.52/1.49  --tptp_safe_out                         true
% 7.52/1.49  --problem_path                          ""
% 7.52/1.49  --include_path                          ""
% 7.52/1.49  --clausifier                            res/vclausify_rel
% 7.52/1.49  --clausifier_options                    ""
% 7.52/1.49  --stdin                                 false
% 7.52/1.49  --stats_out                             all
% 7.52/1.49  
% 7.52/1.49  ------ General Options
% 7.52/1.49  
% 7.52/1.49  --fof                                   false
% 7.52/1.49  --time_out_real                         305.
% 7.52/1.49  --time_out_virtual                      -1.
% 7.52/1.49  --symbol_type_check                     false
% 7.52/1.49  --clausify_out                          false
% 7.52/1.49  --sig_cnt_out                           false
% 7.52/1.49  --trig_cnt_out                          false
% 7.52/1.49  --trig_cnt_out_tolerance                1.
% 7.52/1.49  --trig_cnt_out_sk_spl                   false
% 7.52/1.49  --abstr_cl_out                          false
% 7.52/1.49  
% 7.52/1.49  ------ Global Options
% 7.52/1.49  
% 7.52/1.49  --schedule                              default
% 7.52/1.49  --add_important_lit                     false
% 7.52/1.49  --prop_solver_per_cl                    1000
% 7.52/1.49  --min_unsat_core                        false
% 7.52/1.49  --soft_assumptions                      false
% 7.52/1.49  --soft_lemma_size                       3
% 7.52/1.49  --prop_impl_unit_size                   0
% 7.52/1.49  --prop_impl_unit                        []
% 7.52/1.49  --share_sel_clauses                     true
% 7.52/1.49  --reset_solvers                         false
% 7.52/1.49  --bc_imp_inh                            [conj_cone]
% 7.52/1.49  --conj_cone_tolerance                   3.
% 7.52/1.49  --extra_neg_conj                        none
% 7.52/1.49  --large_theory_mode                     true
% 7.52/1.49  --prolific_symb_bound                   200
% 7.52/1.49  --lt_threshold                          2000
% 7.52/1.49  --clause_weak_htbl                      true
% 7.52/1.49  --gc_record_bc_elim                     false
% 7.52/1.49  
% 7.52/1.49  ------ Preprocessing Options
% 7.52/1.49  
% 7.52/1.49  --preprocessing_flag                    true
% 7.52/1.49  --time_out_prep_mult                    0.1
% 7.52/1.49  --splitting_mode                        input
% 7.52/1.49  --splitting_grd                         true
% 7.52/1.49  --splitting_cvd                         false
% 7.52/1.49  --splitting_cvd_svl                     false
% 7.52/1.49  --splitting_nvd                         32
% 7.52/1.49  --sub_typing                            true
% 7.52/1.49  --prep_gs_sim                           true
% 7.52/1.49  --prep_unflatten                        true
% 7.52/1.49  --prep_res_sim                          true
% 7.52/1.49  --prep_upred                            true
% 7.52/1.49  --prep_sem_filter                       exhaustive
% 7.52/1.49  --prep_sem_filter_out                   false
% 7.52/1.49  --pred_elim                             true
% 7.52/1.49  --res_sim_input                         true
% 7.52/1.49  --eq_ax_congr_red                       true
% 7.52/1.49  --pure_diseq_elim                       true
% 7.52/1.49  --brand_transform                       false
% 7.52/1.49  --non_eq_to_eq                          false
% 7.52/1.49  --prep_def_merge                        true
% 7.52/1.49  --prep_def_merge_prop_impl              false
% 7.52/1.49  --prep_def_merge_mbd                    true
% 7.52/1.49  --prep_def_merge_tr_red                 false
% 7.52/1.49  --prep_def_merge_tr_cl                  false
% 7.52/1.49  --smt_preprocessing                     true
% 7.52/1.49  --smt_ac_axioms                         fast
% 7.52/1.49  --preprocessed_out                      false
% 7.52/1.49  --preprocessed_stats                    false
% 7.52/1.49  
% 7.52/1.49  ------ Abstraction refinement Options
% 7.52/1.49  
% 7.52/1.49  --abstr_ref                             []
% 7.52/1.49  --abstr_ref_prep                        false
% 7.52/1.49  --abstr_ref_until_sat                   false
% 7.52/1.49  --abstr_ref_sig_restrict                funpre
% 7.52/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.52/1.49  --abstr_ref_under                       []
% 7.52/1.49  
% 7.52/1.49  ------ SAT Options
% 7.52/1.49  
% 7.52/1.49  --sat_mode                              false
% 7.52/1.49  --sat_fm_restart_options                ""
% 7.52/1.49  --sat_gr_def                            false
% 7.52/1.49  --sat_epr_types                         true
% 7.52/1.49  --sat_non_cyclic_types                  false
% 7.52/1.49  --sat_finite_models                     false
% 7.52/1.49  --sat_fm_lemmas                         false
% 7.52/1.49  --sat_fm_prep                           false
% 7.52/1.49  --sat_fm_uc_incr                        true
% 7.52/1.49  --sat_out_model                         small
% 7.52/1.49  --sat_out_clauses                       false
% 7.52/1.49  
% 7.52/1.49  ------ QBF Options
% 7.52/1.49  
% 7.52/1.49  --qbf_mode                              false
% 7.52/1.49  --qbf_elim_univ                         false
% 7.52/1.49  --qbf_dom_inst                          none
% 7.52/1.49  --qbf_dom_pre_inst                      false
% 7.52/1.49  --qbf_sk_in                             false
% 7.52/1.49  --qbf_pred_elim                         true
% 7.52/1.49  --qbf_split                             512
% 7.52/1.49  
% 7.52/1.49  ------ BMC1 Options
% 7.52/1.49  
% 7.52/1.49  --bmc1_incremental                      false
% 7.52/1.49  --bmc1_axioms                           reachable_all
% 7.52/1.49  --bmc1_min_bound                        0
% 7.52/1.49  --bmc1_max_bound                        -1
% 7.52/1.49  --bmc1_max_bound_default                -1
% 7.52/1.49  --bmc1_symbol_reachability              true
% 7.52/1.49  --bmc1_property_lemmas                  false
% 7.52/1.49  --bmc1_k_induction                      false
% 7.52/1.49  --bmc1_non_equiv_states                 false
% 7.52/1.49  --bmc1_deadlock                         false
% 7.52/1.49  --bmc1_ucm                              false
% 7.52/1.49  --bmc1_add_unsat_core                   none
% 7.52/1.49  --bmc1_unsat_core_children              false
% 7.52/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.52/1.49  --bmc1_out_stat                         full
% 7.52/1.49  --bmc1_ground_init                      false
% 7.52/1.49  --bmc1_pre_inst_next_state              false
% 7.52/1.49  --bmc1_pre_inst_state                   false
% 7.52/1.49  --bmc1_pre_inst_reach_state             false
% 7.52/1.49  --bmc1_out_unsat_core                   false
% 7.52/1.49  --bmc1_aig_witness_out                  false
% 7.52/1.49  --bmc1_verbose                          false
% 7.52/1.49  --bmc1_dump_clauses_tptp                false
% 7.52/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.52/1.49  --bmc1_dump_file                        -
% 7.52/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.52/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.52/1.49  --bmc1_ucm_extend_mode                  1
% 7.52/1.49  --bmc1_ucm_init_mode                    2
% 7.52/1.49  --bmc1_ucm_cone_mode                    none
% 7.52/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.52/1.49  --bmc1_ucm_relax_model                  4
% 7.52/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.52/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.52/1.49  --bmc1_ucm_layered_model                none
% 7.52/1.49  --bmc1_ucm_max_lemma_size               10
% 7.52/1.49  
% 7.52/1.49  ------ AIG Options
% 7.52/1.49  
% 7.52/1.49  --aig_mode                              false
% 7.52/1.49  
% 7.52/1.49  ------ Instantiation Options
% 7.52/1.49  
% 7.52/1.49  --instantiation_flag                    true
% 7.52/1.49  --inst_sos_flag                         true
% 7.52/1.49  --inst_sos_phase                        true
% 7.52/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.52/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.52/1.49  --inst_lit_sel_side                     num_symb
% 7.52/1.49  --inst_solver_per_active                1400
% 7.52/1.49  --inst_solver_calls_frac                1.
% 7.52/1.49  --inst_passive_queue_type               priority_queues
% 7.52/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.52/1.49  --inst_passive_queues_freq              [25;2]
% 7.52/1.49  --inst_dismatching                      true
% 7.52/1.49  --inst_eager_unprocessed_to_passive     true
% 7.52/1.49  --inst_prop_sim_given                   true
% 7.52/1.49  --inst_prop_sim_new                     false
% 7.52/1.49  --inst_subs_new                         false
% 7.52/1.49  --inst_eq_res_simp                      false
% 7.52/1.49  --inst_subs_given                       false
% 7.52/1.49  --inst_orphan_elimination               true
% 7.52/1.49  --inst_learning_loop_flag               true
% 7.52/1.49  --inst_learning_start                   3000
% 7.52/1.49  --inst_learning_factor                  2
% 7.52/1.49  --inst_start_prop_sim_after_learn       3
% 7.52/1.49  --inst_sel_renew                        solver
% 7.52/1.49  --inst_lit_activity_flag                true
% 7.52/1.49  --inst_restr_to_given                   false
% 7.52/1.49  --inst_activity_threshold               500
% 7.52/1.49  --inst_out_proof                        true
% 7.52/1.49  
% 7.52/1.49  ------ Resolution Options
% 7.52/1.49  
% 7.52/1.49  --resolution_flag                       true
% 7.52/1.49  --res_lit_sel                           adaptive
% 7.52/1.49  --res_lit_sel_side                      none
% 7.52/1.49  --res_ordering                          kbo
% 7.52/1.49  --res_to_prop_solver                    active
% 7.52/1.49  --res_prop_simpl_new                    false
% 7.52/1.49  --res_prop_simpl_given                  true
% 7.52/1.49  --res_passive_queue_type                priority_queues
% 7.52/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.52/1.49  --res_passive_queues_freq               [15;5]
% 7.52/1.49  --res_forward_subs                      full
% 7.52/1.49  --res_backward_subs                     full
% 7.52/1.49  --res_forward_subs_resolution           true
% 7.52/1.49  --res_backward_subs_resolution          true
% 7.52/1.49  --res_orphan_elimination                true
% 7.52/1.49  --res_time_limit                        2.
% 7.52/1.49  --res_out_proof                         true
% 7.52/1.49  
% 7.52/1.49  ------ Superposition Options
% 7.52/1.49  
% 7.52/1.49  --superposition_flag                    true
% 7.52/1.49  --sup_passive_queue_type                priority_queues
% 7.52/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.52/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.52/1.49  --demod_completeness_check              fast
% 7.52/1.49  --demod_use_ground                      true
% 7.52/1.49  --sup_to_prop_solver                    passive
% 7.52/1.49  --sup_prop_simpl_new                    true
% 7.52/1.49  --sup_prop_simpl_given                  true
% 7.52/1.49  --sup_fun_splitting                     true
% 7.52/1.49  --sup_smt_interval                      50000
% 7.52/1.49  
% 7.52/1.49  ------ Superposition Simplification Setup
% 7.52/1.49  
% 7.52/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.52/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.52/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.52/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.52/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.52/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.52/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.52/1.49  --sup_immed_triv                        [TrivRules]
% 7.52/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.52/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.52/1.49  --sup_immed_bw_main                     []
% 7.52/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.52/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.52/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.52/1.49  --sup_input_bw                          []
% 7.52/1.49  
% 7.52/1.49  ------ Combination Options
% 7.52/1.49  
% 7.52/1.49  --comb_res_mult                         3
% 7.52/1.49  --comb_sup_mult                         2
% 7.52/1.49  --comb_inst_mult                        10
% 7.52/1.49  
% 7.52/1.49  ------ Debug Options
% 7.52/1.49  
% 7.52/1.49  --dbg_backtrace                         false
% 7.52/1.49  --dbg_dump_prop_clauses                 false
% 7.52/1.49  --dbg_dump_prop_clauses_file            -
% 7.52/1.49  --dbg_out_stat                          false
% 7.52/1.49  ------ Parsing...
% 7.52/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.52/1.49  
% 7.52/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 7.52/1.49  
% 7.52/1.49  ------ Preprocessing... gs_s  sp: 8 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.52/1.49  
% 7.52/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.52/1.49  ------ Proving...
% 7.52/1.49  ------ Problem Properties 
% 7.52/1.49  
% 7.52/1.49  
% 7.52/1.49  clauses                                 26
% 7.52/1.49  conjectures                             2
% 7.52/1.49  EPR                                     6
% 7.52/1.49  Horn                                    19
% 7.52/1.49  unary                                   5
% 7.52/1.49  binary                                  14
% 7.52/1.49  lits                                    55
% 7.52/1.49  lits eq                                 27
% 7.52/1.49  fd_pure                                 0
% 7.52/1.49  fd_pseudo                               0
% 7.52/1.49  fd_cond                                 0
% 7.52/1.49  fd_pseudo_cond                          3
% 7.52/1.49  AC symbols                              0
% 7.52/1.49  
% 7.52/1.49  ------ Schedule dynamic 5 is on 
% 7.52/1.49  
% 7.52/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.52/1.49  
% 7.52/1.49  
% 7.52/1.49  ------ 
% 7.52/1.49  Current options:
% 7.52/1.49  ------ 
% 7.52/1.49  
% 7.52/1.49  ------ Input Options
% 7.52/1.49  
% 7.52/1.49  --out_options                           all
% 7.52/1.49  --tptp_safe_out                         true
% 7.52/1.49  --problem_path                          ""
% 7.52/1.49  --include_path                          ""
% 7.52/1.49  --clausifier                            res/vclausify_rel
% 7.52/1.49  --clausifier_options                    ""
% 7.52/1.49  --stdin                                 false
% 7.52/1.49  --stats_out                             all
% 7.52/1.49  
% 7.52/1.49  ------ General Options
% 7.52/1.49  
% 7.52/1.49  --fof                                   false
% 7.52/1.49  --time_out_real                         305.
% 7.52/1.49  --time_out_virtual                      -1.
% 7.52/1.49  --symbol_type_check                     false
% 7.52/1.49  --clausify_out                          false
% 7.52/1.49  --sig_cnt_out                           false
% 7.52/1.49  --trig_cnt_out                          false
% 7.52/1.49  --trig_cnt_out_tolerance                1.
% 7.52/1.49  --trig_cnt_out_sk_spl                   false
% 7.52/1.49  --abstr_cl_out                          false
% 7.52/1.49  
% 7.52/1.49  ------ Global Options
% 7.52/1.49  
% 7.52/1.49  --schedule                              default
% 7.52/1.49  --add_important_lit                     false
% 7.52/1.49  --prop_solver_per_cl                    1000
% 7.52/1.49  --min_unsat_core                        false
% 7.52/1.49  --soft_assumptions                      false
% 7.52/1.49  --soft_lemma_size                       3
% 7.52/1.49  --prop_impl_unit_size                   0
% 7.52/1.49  --prop_impl_unit                        []
% 7.52/1.49  --share_sel_clauses                     true
% 7.52/1.49  --reset_solvers                         false
% 7.52/1.49  --bc_imp_inh                            [conj_cone]
% 7.52/1.49  --conj_cone_tolerance                   3.
% 7.52/1.49  --extra_neg_conj                        none
% 7.52/1.49  --large_theory_mode                     true
% 7.52/1.49  --prolific_symb_bound                   200
% 7.52/1.49  --lt_threshold                          2000
% 7.52/1.49  --clause_weak_htbl                      true
% 7.52/1.49  --gc_record_bc_elim                     false
% 7.52/1.49  
% 7.52/1.49  ------ Preprocessing Options
% 7.52/1.49  
% 7.52/1.49  --preprocessing_flag                    true
% 7.52/1.49  --time_out_prep_mult                    0.1
% 7.52/1.49  --splitting_mode                        input
% 7.52/1.49  --splitting_grd                         true
% 7.52/1.49  --splitting_cvd                         false
% 7.52/1.49  --splitting_cvd_svl                     false
% 7.52/1.49  --splitting_nvd                         32
% 7.52/1.49  --sub_typing                            true
% 7.52/1.49  --prep_gs_sim                           true
% 7.52/1.49  --prep_unflatten                        true
% 7.52/1.49  --prep_res_sim                          true
% 7.52/1.49  --prep_upred                            true
% 7.52/1.49  --prep_sem_filter                       exhaustive
% 7.52/1.49  --prep_sem_filter_out                   false
% 7.52/1.49  --pred_elim                             true
% 7.52/1.49  --res_sim_input                         true
% 7.52/1.49  --eq_ax_congr_red                       true
% 7.52/1.49  --pure_diseq_elim                       true
% 7.52/1.49  --brand_transform                       false
% 7.52/1.49  --non_eq_to_eq                          false
% 7.52/1.49  --prep_def_merge                        true
% 7.52/1.49  --prep_def_merge_prop_impl              false
% 7.52/1.49  --prep_def_merge_mbd                    true
% 7.52/1.49  --prep_def_merge_tr_red                 false
% 7.52/1.49  --prep_def_merge_tr_cl                  false
% 7.52/1.49  --smt_preprocessing                     true
% 7.52/1.49  --smt_ac_axioms                         fast
% 7.52/1.49  --preprocessed_out                      false
% 7.52/1.49  --preprocessed_stats                    false
% 7.52/1.49  
% 7.52/1.49  ------ Abstraction refinement Options
% 7.52/1.49  
% 7.52/1.49  --abstr_ref                             []
% 7.52/1.49  --abstr_ref_prep                        false
% 7.52/1.49  --abstr_ref_until_sat                   false
% 7.52/1.49  --abstr_ref_sig_restrict                funpre
% 7.52/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.52/1.49  --abstr_ref_under                       []
% 7.52/1.49  
% 7.52/1.49  ------ SAT Options
% 7.52/1.49  
% 7.52/1.49  --sat_mode                              false
% 7.52/1.49  --sat_fm_restart_options                ""
% 7.52/1.49  --sat_gr_def                            false
% 7.52/1.49  --sat_epr_types                         true
% 7.52/1.49  --sat_non_cyclic_types                  false
% 7.52/1.49  --sat_finite_models                     false
% 7.52/1.49  --sat_fm_lemmas                         false
% 7.52/1.49  --sat_fm_prep                           false
% 7.52/1.49  --sat_fm_uc_incr                        true
% 7.52/1.49  --sat_out_model                         small
% 7.52/1.49  --sat_out_clauses                       false
% 7.52/1.49  
% 7.52/1.49  ------ QBF Options
% 7.52/1.49  
% 7.52/1.49  --qbf_mode                              false
% 7.52/1.49  --qbf_elim_univ                         false
% 7.52/1.49  --qbf_dom_inst                          none
% 7.52/1.49  --qbf_dom_pre_inst                      false
% 7.52/1.49  --qbf_sk_in                             false
% 7.52/1.49  --qbf_pred_elim                         true
% 7.52/1.49  --qbf_split                             512
% 7.52/1.49  
% 7.52/1.49  ------ BMC1 Options
% 7.52/1.49  
% 7.52/1.49  --bmc1_incremental                      false
% 7.52/1.49  --bmc1_axioms                           reachable_all
% 7.52/1.49  --bmc1_min_bound                        0
% 7.52/1.49  --bmc1_max_bound                        -1
% 7.52/1.49  --bmc1_max_bound_default                -1
% 7.52/1.49  --bmc1_symbol_reachability              true
% 7.52/1.49  --bmc1_property_lemmas                  false
% 7.52/1.49  --bmc1_k_induction                      false
% 7.52/1.49  --bmc1_non_equiv_states                 false
% 7.52/1.49  --bmc1_deadlock                         false
% 7.52/1.49  --bmc1_ucm                              false
% 7.52/1.49  --bmc1_add_unsat_core                   none
% 7.52/1.49  --bmc1_unsat_core_children              false
% 7.52/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.52/1.49  --bmc1_out_stat                         full
% 7.52/1.49  --bmc1_ground_init                      false
% 7.52/1.49  --bmc1_pre_inst_next_state              false
% 7.52/1.49  --bmc1_pre_inst_state                   false
% 7.52/1.49  --bmc1_pre_inst_reach_state             false
% 7.52/1.49  --bmc1_out_unsat_core                   false
% 7.52/1.49  --bmc1_aig_witness_out                  false
% 7.52/1.49  --bmc1_verbose                          false
% 7.52/1.49  --bmc1_dump_clauses_tptp                false
% 7.52/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.52/1.49  --bmc1_dump_file                        -
% 7.52/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.52/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.52/1.49  --bmc1_ucm_extend_mode                  1
% 7.52/1.49  --bmc1_ucm_init_mode                    2
% 7.52/1.49  --bmc1_ucm_cone_mode                    none
% 7.52/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.52/1.49  --bmc1_ucm_relax_model                  4
% 7.52/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.52/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.52/1.49  --bmc1_ucm_layered_model                none
% 7.52/1.49  --bmc1_ucm_max_lemma_size               10
% 7.52/1.49  
% 7.52/1.49  ------ AIG Options
% 7.52/1.49  
% 7.52/1.49  --aig_mode                              false
% 7.52/1.49  
% 7.52/1.49  ------ Instantiation Options
% 7.52/1.49  
% 7.52/1.49  --instantiation_flag                    true
% 7.52/1.49  --inst_sos_flag                         true
% 7.52/1.49  --inst_sos_phase                        true
% 7.52/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.52/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.52/1.49  --inst_lit_sel_side                     none
% 7.52/1.49  --inst_solver_per_active                1400
% 7.52/1.49  --inst_solver_calls_frac                1.
% 7.52/1.49  --inst_passive_queue_type               priority_queues
% 7.52/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.52/1.49  --inst_passive_queues_freq              [25;2]
% 7.52/1.49  --inst_dismatching                      true
% 7.52/1.49  --inst_eager_unprocessed_to_passive     true
% 7.52/1.49  --inst_prop_sim_given                   true
% 7.52/1.49  --inst_prop_sim_new                     false
% 7.52/1.49  --inst_subs_new                         false
% 7.52/1.49  --inst_eq_res_simp                      false
% 7.52/1.49  --inst_subs_given                       false
% 7.52/1.49  --inst_orphan_elimination               true
% 7.52/1.49  --inst_learning_loop_flag               true
% 7.52/1.49  --inst_learning_start                   3000
% 7.52/1.49  --inst_learning_factor                  2
% 7.52/1.49  --inst_start_prop_sim_after_learn       3
% 7.52/1.49  --inst_sel_renew                        solver
% 7.52/1.49  --inst_lit_activity_flag                true
% 7.52/1.49  --inst_restr_to_given                   false
% 7.52/1.49  --inst_activity_threshold               500
% 7.52/1.49  --inst_out_proof                        true
% 7.52/1.49  
% 7.52/1.49  ------ Resolution Options
% 7.52/1.49  
% 7.52/1.49  --resolution_flag                       false
% 7.52/1.49  --res_lit_sel                           adaptive
% 7.52/1.49  --res_lit_sel_side                      none
% 7.52/1.49  --res_ordering                          kbo
% 7.52/1.49  --res_to_prop_solver                    active
% 7.52/1.49  --res_prop_simpl_new                    false
% 7.52/1.49  --res_prop_simpl_given                  true
% 7.52/1.49  --res_passive_queue_type                priority_queues
% 7.52/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.52/1.49  --res_passive_queues_freq               [15;5]
% 7.52/1.49  --res_forward_subs                      full
% 7.52/1.49  --res_backward_subs                     full
% 7.52/1.49  --res_forward_subs_resolution           true
% 7.52/1.49  --res_backward_subs_resolution          true
% 7.52/1.49  --res_orphan_elimination                true
% 7.52/1.49  --res_time_limit                        2.
% 7.52/1.49  --res_out_proof                         true
% 7.52/1.49  
% 7.52/1.49  ------ Superposition Options
% 7.52/1.49  
% 7.52/1.49  --superposition_flag                    true
% 7.52/1.49  --sup_passive_queue_type                priority_queues
% 7.52/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.52/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.52/1.49  --demod_completeness_check              fast
% 7.52/1.49  --demod_use_ground                      true
% 7.52/1.49  --sup_to_prop_solver                    passive
% 7.52/1.49  --sup_prop_simpl_new                    true
% 7.52/1.49  --sup_prop_simpl_given                  true
% 7.52/1.49  --sup_fun_splitting                     true
% 7.52/1.49  --sup_smt_interval                      50000
% 7.52/1.49  
% 7.52/1.49  ------ Superposition Simplification Setup
% 7.52/1.49  
% 7.52/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.52/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.52/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.52/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.52/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.52/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.52/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.52/1.49  --sup_immed_triv                        [TrivRules]
% 7.52/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.52/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.52/1.49  --sup_immed_bw_main                     []
% 7.52/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.52/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.52/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.52/1.49  --sup_input_bw                          []
% 7.52/1.49  
% 7.52/1.49  ------ Combination Options
% 7.52/1.49  
% 7.52/1.49  --comb_res_mult                         3
% 7.52/1.49  --comb_sup_mult                         2
% 7.52/1.49  --comb_inst_mult                        10
% 7.52/1.49  
% 7.52/1.49  ------ Debug Options
% 7.52/1.49  
% 7.52/1.49  --dbg_backtrace                         false
% 7.52/1.49  --dbg_dump_prop_clauses                 false
% 7.52/1.49  --dbg_dump_prop_clauses_file            -
% 7.52/1.49  --dbg_out_stat                          false
% 7.52/1.49  
% 7.52/1.49  
% 7.52/1.49  
% 7.52/1.49  
% 7.52/1.49  ------ Proving...
% 7.52/1.49  
% 7.52/1.49  
% 7.52/1.49  % SZS status Theorem for theBenchmark.p
% 7.52/1.49  
% 7.52/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.52/1.49  
% 7.52/1.49  fof(f1,axiom,(
% 7.52/1.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.52/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.49  
% 7.52/1.49  fof(f38,plain,(
% 7.52/1.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.52/1.49    inference(cnf_transformation,[],[f1])).
% 7.52/1.49  
% 7.52/1.49  fof(f9,axiom,(
% 7.52/1.49    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 7.52/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.49  
% 7.52/1.49  fof(f21,plain,(
% 7.52/1.49    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 7.52/1.49    inference(ennf_transformation,[],[f9])).
% 7.52/1.49  
% 7.52/1.49  fof(f52,plain,(
% 7.52/1.49    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 7.52/1.49    inference(cnf_transformation,[],[f21])).
% 7.52/1.49  
% 7.52/1.49  fof(f7,axiom,(
% 7.52/1.49    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 7.52/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.49  
% 7.52/1.49  fof(f18,plain,(
% 7.52/1.49    ! [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 7.52/1.49    inference(ennf_transformation,[],[f7])).
% 7.52/1.49  
% 7.52/1.49  fof(f35,plain,(
% 7.52/1.49    ! [X0,X1] : (((r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0)) & (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)))) | ~v1_relat_1(X1))),
% 7.52/1.49    inference(nnf_transformation,[],[f18])).
% 7.52/1.49  
% 7.52/1.49  fof(f50,plain,(
% 7.52/1.49    ( ! [X0,X1] : (r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.52/1.49    inference(cnf_transformation,[],[f35])).
% 7.52/1.49  
% 7.52/1.49  fof(f10,axiom,(
% 7.52/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.52/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.49  
% 7.52/1.49  fof(f22,plain,(
% 7.52/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.52/1.49    inference(ennf_transformation,[],[f10])).
% 7.52/1.49  
% 7.52/1.49  fof(f53,plain,(
% 7.52/1.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.52/1.49    inference(cnf_transformation,[],[f22])).
% 7.52/1.49  
% 7.52/1.49  fof(f15,conjecture,(
% 7.52/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 7.52/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.49  
% 7.52/1.49  fof(f16,negated_conjecture,(
% 7.52/1.49    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 7.52/1.49    inference(negated_conjecture,[],[f15])).
% 7.52/1.49  
% 7.52/1.49  fof(f28,plain,(
% 7.52/1.49    ? [X0,X1,X2] : ((k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 7.52/1.49    inference(ennf_transformation,[],[f16])).
% 7.52/1.49  
% 7.52/1.49  fof(f29,plain,(
% 7.52/1.49    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 7.52/1.49    inference(flattening,[],[f28])).
% 7.52/1.49  
% 7.52/1.49  fof(f36,plain,(
% 7.52/1.49    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_tarski(k1_funct_1(sK3,sK1)) != k2_relset_1(k1_tarski(sK1),sK2,sK3) & k1_xboole_0 != sK2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK3,k1_tarski(sK1),sK2) & v1_funct_1(sK3))),
% 7.52/1.49    introduced(choice_axiom,[])).
% 7.52/1.49  
% 7.52/1.49  fof(f37,plain,(
% 7.52/1.49    k1_tarski(k1_funct_1(sK3,sK1)) != k2_relset_1(k1_tarski(sK1),sK2,sK3) & k1_xboole_0 != sK2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK3,k1_tarski(sK1),sK2) & v1_funct_1(sK3)),
% 7.52/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f29,f36])).
% 7.52/1.49  
% 7.52/1.49  fof(f61,plain,(
% 7.52/1.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))),
% 7.52/1.49    inference(cnf_transformation,[],[f37])).
% 7.52/1.49  
% 7.52/1.49  fof(f3,axiom,(
% 7.52/1.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.52/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.49  
% 7.52/1.49  fof(f45,plain,(
% 7.52/1.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.52/1.49    inference(cnf_transformation,[],[f3])).
% 7.52/1.49  
% 7.52/1.49  fof(f4,axiom,(
% 7.52/1.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.52/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.49  
% 7.52/1.49  fof(f46,plain,(
% 7.52/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.52/1.49    inference(cnf_transformation,[],[f4])).
% 7.52/1.49  
% 7.52/1.49  fof(f5,axiom,(
% 7.52/1.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.52/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.49  
% 7.52/1.49  fof(f47,plain,(
% 7.52/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.52/1.49    inference(cnf_transformation,[],[f5])).
% 7.52/1.49  
% 7.52/1.49  fof(f64,plain,(
% 7.52/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 7.52/1.49    inference(definition_unfolding,[],[f46,f47])).
% 7.52/1.49  
% 7.52/1.49  fof(f65,plain,(
% 7.52/1.49    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 7.52/1.49    inference(definition_unfolding,[],[f45,f64])).
% 7.52/1.49  
% 7.52/1.49  fof(f75,plain,(
% 7.52/1.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))),
% 7.52/1.49    inference(definition_unfolding,[],[f61,f65])).
% 7.52/1.49  
% 7.52/1.49  fof(f8,axiom,(
% 7.52/1.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)))),
% 7.52/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.49  
% 7.52/1.49  fof(f19,plain,(
% 7.52/1.49    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.52/1.49    inference(ennf_transformation,[],[f8])).
% 7.52/1.49  
% 7.52/1.49  fof(f20,plain,(
% 7.52/1.49    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.52/1.49    inference(flattening,[],[f19])).
% 7.52/1.49  
% 7.52/1.49  fof(f51,plain,(
% 7.52/1.49    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.52/1.49    inference(cnf_transformation,[],[f20])).
% 7.52/1.49  
% 7.52/1.49  fof(f73,plain,(
% 7.52/1.49    ( ! [X0,X1] : (k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.52/1.49    inference(definition_unfolding,[],[f51,f65])).
% 7.52/1.49  
% 7.52/1.49  fof(f59,plain,(
% 7.52/1.49    v1_funct_1(sK3)),
% 7.52/1.49    inference(cnf_transformation,[],[f37])).
% 7.52/1.49  
% 7.52/1.49  fof(f11,axiom,(
% 7.52/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 7.52/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.49  
% 7.52/1.49  fof(f23,plain,(
% 7.52/1.49    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.52/1.49    inference(ennf_transformation,[],[f11])).
% 7.52/1.49  
% 7.52/1.49  fof(f54,plain,(
% 7.52/1.49    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.52/1.49    inference(cnf_transformation,[],[f23])).
% 7.52/1.49  
% 7.52/1.49  fof(f63,plain,(
% 7.52/1.49    k1_tarski(k1_funct_1(sK3,sK1)) != k2_relset_1(k1_tarski(sK1),sK2,sK3)),
% 7.52/1.49    inference(cnf_transformation,[],[f37])).
% 7.52/1.49  
% 7.52/1.49  fof(f74,plain,(
% 7.52/1.49    k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3)),
% 7.52/1.49    inference(definition_unfolding,[],[f63,f65,f65])).
% 7.52/1.49  
% 7.52/1.49  fof(f6,axiom,(
% 7.52/1.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 7.52/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.49  
% 7.52/1.49  fof(f17,plain,(
% 7.52/1.49    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 7.52/1.49    inference(ennf_transformation,[],[f6])).
% 7.52/1.49  
% 7.52/1.49  fof(f48,plain,(
% 7.52/1.49    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 7.52/1.49    inference(cnf_transformation,[],[f17])).
% 7.52/1.49  
% 7.52/1.49  fof(f72,plain,(
% 7.52/1.49    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 7.52/1.49    inference(definition_unfolding,[],[f48,f65])).
% 7.52/1.49  
% 7.52/1.49  fof(f12,axiom,(
% 7.52/1.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 7.52/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.49  
% 7.52/1.49  fof(f24,plain,(
% 7.52/1.49    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.52/1.49    inference(ennf_transformation,[],[f12])).
% 7.52/1.49  
% 7.52/1.49  fof(f55,plain,(
% 7.52/1.49    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.52/1.49    inference(cnf_transformation,[],[f24])).
% 7.52/1.49  
% 7.52/1.49  fof(f13,axiom,(
% 7.52/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 7.52/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.49  
% 7.52/1.49  fof(f25,plain,(
% 7.52/1.49    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.52/1.49    inference(ennf_transformation,[],[f13])).
% 7.52/1.49  
% 7.52/1.49  fof(f56,plain,(
% 7.52/1.49    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.52/1.49    inference(cnf_transformation,[],[f25])).
% 7.52/1.49  
% 7.52/1.49  fof(f2,axiom,(
% 7.52/1.49    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 7.52/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.49  
% 7.52/1.49  fof(f30,plain,(
% 7.52/1.49    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 7.52/1.49    inference(nnf_transformation,[],[f2])).
% 7.52/1.49  
% 7.52/1.49  fof(f31,plain,(
% 7.52/1.49    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 7.52/1.49    inference(flattening,[],[f30])).
% 7.52/1.49  
% 7.52/1.49  fof(f32,plain,(
% 7.52/1.49    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 7.52/1.49    inference(rectify,[],[f31])).
% 7.52/1.49  
% 7.52/1.49  fof(f33,plain,(
% 7.52/1.49    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2))))),
% 7.52/1.49    introduced(choice_axiom,[])).
% 7.52/1.49  
% 7.52/1.49  fof(f34,plain,(
% 7.52/1.49    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 7.52/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).
% 7.52/1.49  
% 7.52/1.49  fof(f41,plain,(
% 7.52/1.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 7.52/1.49    inference(cnf_transformation,[],[f34])).
% 7.52/1.49  
% 7.52/1.49  fof(f69,plain,(
% 7.52/1.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 7.52/1.49    inference(definition_unfolding,[],[f41,f64])).
% 7.52/1.49  
% 7.52/1.49  fof(f77,plain,(
% 7.52/1.49    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X4) != X2) )),
% 7.52/1.49    inference(equality_resolution,[],[f69])).
% 7.52/1.49  
% 7.52/1.49  fof(f78,plain,(
% 7.52/1.49    ( ! [X4,X0] : (r2_hidden(X4,k2_enumset1(X0,X0,X0,X4))) )),
% 7.52/1.49    inference(equality_resolution,[],[f77])).
% 7.52/1.49  
% 7.52/1.49  fof(f14,axiom,(
% 7.52/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 7.52/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.49  
% 7.52/1.49  fof(f26,plain,(
% 7.52/1.49    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 7.52/1.49    inference(ennf_transformation,[],[f14])).
% 7.52/1.49  
% 7.52/1.49  fof(f27,plain,(
% 7.52/1.49    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 7.52/1.49    inference(flattening,[],[f26])).
% 7.52/1.49  
% 7.52/1.49  fof(f58,plain,(
% 7.52/1.49    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.52/1.49    inference(cnf_transformation,[],[f27])).
% 7.52/1.49  
% 7.52/1.49  fof(f60,plain,(
% 7.52/1.49    v1_funct_2(sK3,k1_tarski(sK1),sK2)),
% 7.52/1.49    inference(cnf_transformation,[],[f37])).
% 7.52/1.49  
% 7.52/1.49  fof(f76,plain,(
% 7.52/1.49    v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2)),
% 7.52/1.49    inference(definition_unfolding,[],[f60,f65])).
% 7.52/1.49  
% 7.52/1.49  fof(f62,plain,(
% 7.52/1.49    k1_xboole_0 != sK2),
% 7.52/1.49    inference(cnf_transformation,[],[f37])).
% 7.52/1.49  
% 7.52/1.49  cnf(c_0,plain,
% 7.52/1.49      ( r1_tarski(k1_xboole_0,X0) ),
% 7.52/1.49      inference(cnf_transformation,[],[f38]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_11,plain,
% 7.52/1.49      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 7.52/1.49      inference(cnf_transformation,[],[f52]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_244,plain,
% 7.52/1.49      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 7.52/1.49      inference(resolution_lifted,[status(thm)],[c_0,c_11]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_245,plain,
% 7.52/1.49      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 7.52/1.49      inference(unflattening,[status(thm)],[c_244]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_14885,plain,
% 7.52/1.49      ( ~ r2_hidden(k1_funct_1(sK3,X0),k1_xboole_0) ),
% 7.52/1.49      inference(instantiation,[status(thm)],[c_245]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_14887,plain,
% 7.52/1.49      ( ~ r2_hidden(k1_funct_1(sK3,sK1),k1_xboole_0) ),
% 7.52/1.49      inference(instantiation,[status(thm)],[c_14885]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_8,plain,
% 7.52/1.49      ( r2_hidden(X0,k1_relat_1(X1))
% 7.52/1.49      | ~ v1_relat_1(X1)
% 7.52/1.49      | k11_relat_1(X1,X0) = k1_xboole_0 ),
% 7.52/1.49      inference(cnf_transformation,[],[f50]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_12,plain,
% 7.52/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.52/1.49      | v1_relat_1(X0) ),
% 7.52/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_20,negated_conjecture,
% 7.52/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
% 7.52/1.49      inference(cnf_transformation,[],[f75]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_331,plain,
% 7.52/1.49      ( v1_relat_1(X0)
% 7.52/1.49      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 7.52/1.49      | sK3 != X0 ),
% 7.52/1.49      inference(resolution_lifted,[status(thm)],[c_12,c_20]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_332,plain,
% 7.52/1.49      ( v1_relat_1(sK3)
% 7.52/1.49      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 7.52/1.49      inference(unflattening,[status(thm)],[c_331]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_392,plain,
% 7.52/1.49      ( r2_hidden(X0,k1_relat_1(X1))
% 7.52/1.49      | k11_relat_1(X1,X0) = k1_xboole_0
% 7.52/1.49      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
% 7.52/1.49      | sK3 != X1 ),
% 7.52/1.49      inference(resolution_lifted,[status(thm)],[c_8,c_332]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_393,plain,
% 7.52/1.49      ( r2_hidden(X0,k1_relat_1(sK3))
% 7.52/1.49      | k11_relat_1(sK3,X0) = k1_xboole_0
% 7.52/1.49      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
% 7.52/1.49      inference(unflattening,[status(thm)],[c_392]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_505,plain,
% 7.52/1.49      ( r2_hidden(X0,k1_relat_1(sK3))
% 7.52/1.49      | k11_relat_1(sK3,X0) = k1_xboole_0
% 7.52/1.49      | ~ sP1_iProver_split ),
% 7.52/1.49      inference(splitting,
% 7.52/1.49                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 7.52/1.49                [c_393]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_821,plain,
% 7.52/1.49      ( k11_relat_1(sK3,X0) = k1_xboole_0
% 7.52/1.49      | r2_hidden(X0,k1_relat_1(sK3)) = iProver_top
% 7.52/1.49      | sP1_iProver_split != iProver_top ),
% 7.52/1.49      inference(predicate_to_equality,[status(thm)],[c_505]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_506,plain,
% 7.52/1.49      ( sP1_iProver_split | sP0_iProver_split ),
% 7.52/1.49      inference(splitting,
% 7.52/1.49                [splitting(split),new_symbols(definition,[])],
% 7.52/1.49                [c_393]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_544,plain,
% 7.52/1.49      ( sP1_iProver_split = iProver_top
% 7.52/1.49      | sP0_iProver_split = iProver_top ),
% 7.52/1.49      inference(predicate_to_equality,[status(thm)],[c_506]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_545,plain,
% 7.52/1.49      ( k11_relat_1(sK3,X0) = k1_xboole_0
% 7.52/1.49      | r2_hidden(X0,k1_relat_1(sK3)) = iProver_top
% 7.52/1.49      | sP1_iProver_split != iProver_top ),
% 7.52/1.49      inference(predicate_to_equality,[status(thm)],[c_505]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_504,plain,
% 7.52/1.49      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 7.52/1.49      | ~ sP0_iProver_split ),
% 7.52/1.49      inference(splitting,
% 7.52/1.49                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 7.52/1.49                [c_393]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_912,plain,
% 7.52/1.49      ( ~ sP0_iProver_split
% 7.52/1.49      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
% 7.52/1.49      inference(instantiation,[status(thm)],[c_504]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_913,plain,
% 7.52/1.49      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))
% 7.52/1.49      | sP0_iProver_split != iProver_top ),
% 7.52/1.49      inference(predicate_to_equality,[status(thm)],[c_912]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_514,plain,( X0 = X0 ),theory(equality) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_963,plain,
% 7.52/1.49      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) = k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
% 7.52/1.49      inference(instantiation,[status(thm)],[c_514]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_1133,plain,
% 7.52/1.49      ( r2_hidden(X0,k1_relat_1(sK3)) = iProver_top
% 7.52/1.49      | k11_relat_1(sK3,X0) = k1_xboole_0 ),
% 7.52/1.49      inference(global_propositional_subsumption,
% 7.52/1.49                [status(thm)],
% 7.52/1.49                [c_821,c_544,c_545,c_913,c_963]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_1134,plain,
% 7.52/1.49      ( k11_relat_1(sK3,X0) = k1_xboole_0
% 7.52/1.49      | r2_hidden(X0,k1_relat_1(sK3)) = iProver_top ),
% 7.52/1.49      inference(renaming,[status(thm)],[c_1133]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_10,plain,
% 7.52/1.49      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.52/1.49      | ~ v1_funct_1(X1)
% 7.52/1.49      | ~ v1_relat_1(X1)
% 7.52/1.49      | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ),
% 7.52/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_22,negated_conjecture,
% 7.52/1.49      ( v1_funct_1(sK3) ),
% 7.52/1.49      inference(cnf_transformation,[],[f59]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_276,plain,
% 7.52/1.49      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.52/1.49      | ~ v1_relat_1(X1)
% 7.52/1.49      | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
% 7.52/1.49      | sK3 != X1 ),
% 7.52/1.49      inference(resolution_lifted,[status(thm)],[c_10,c_22]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_277,plain,
% 7.52/1.49      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 7.52/1.49      | ~ v1_relat_1(sK3)
% 7.52/1.49      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0) ),
% 7.52/1.49      inference(unflattening,[status(thm)],[c_276]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_354,plain,
% 7.52/1.49      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 7.52/1.49      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
% 7.52/1.49      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
% 7.52/1.49      inference(resolution,[status(thm)],[c_332,c_277]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_511,plain,
% 7.52/1.49      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 7.52/1.49      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
% 7.52/1.49      | ~ sP4_iProver_split ),
% 7.52/1.49      inference(splitting,
% 7.52/1.49                [splitting(split),new_symbols(definition,[sP4_iProver_split])],
% 7.52/1.49                [c_354]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_830,plain,
% 7.52/1.49      ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
% 7.52/1.49      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 7.52/1.49      | sP4_iProver_split != iProver_top ),
% 7.52/1.49      inference(predicate_to_equality,[status(thm)],[c_511]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_512,plain,
% 7.52/1.49      ( sP4_iProver_split | sP0_iProver_split ),
% 7.52/1.49      inference(splitting,
% 7.52/1.49                [splitting(split),new_symbols(definition,[])],
% 7.52/1.49                [c_354]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_561,plain,
% 7.52/1.49      ( sP4_iProver_split = iProver_top
% 7.52/1.49      | sP0_iProver_split = iProver_top ),
% 7.52/1.49      inference(predicate_to_equality,[status(thm)],[c_512]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_562,plain,
% 7.52/1.49      ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
% 7.52/1.49      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 7.52/1.49      | sP4_iProver_split != iProver_top ),
% 7.52/1.49      inference(predicate_to_equality,[status(thm)],[c_511]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_1623,plain,
% 7.52/1.49      ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 7.52/1.49      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0) ),
% 7.52/1.49      inference(global_propositional_subsumption,
% 7.52/1.49                [status(thm)],
% 7.52/1.49                [c_830,c_561,c_562,c_913,c_963]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_1624,plain,
% 7.52/1.49      ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
% 7.52/1.49      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top ),
% 7.52/1.49      inference(renaming,[status(thm)],[c_1623]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_1629,plain,
% 7.52/1.49      ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
% 7.52/1.49      | k11_relat_1(sK3,X0) = k1_xboole_0 ),
% 7.52/1.49      inference(superposition,[status(thm)],[c_1134,c_1624]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_13,plain,
% 7.52/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.52/1.49      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.52/1.49      inference(cnf_transformation,[],[f54]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_322,plain,
% 7.52/1.49      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.52/1.49      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 7.52/1.49      | sK3 != X2 ),
% 7.52/1.49      inference(resolution_lifted,[status(thm)],[c_13,c_20]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_323,plain,
% 7.52/1.49      ( k2_relset_1(X0,X1,sK3) = k2_relat_1(sK3)
% 7.52/1.49      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 7.52/1.49      inference(unflattening,[status(thm)],[c_322]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_930,plain,
% 7.52/1.49      ( k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) = k2_relat_1(sK3) ),
% 7.52/1.49      inference(equality_resolution,[status(thm)],[c_323]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_18,negated_conjecture,
% 7.52/1.49      ( k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) ),
% 7.52/1.49      inference(cnf_transformation,[],[f74]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_1085,plain,
% 7.52/1.49      ( k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relat_1(sK3) ),
% 7.52/1.49      inference(demodulation,[status(thm)],[c_930,c_18]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_2019,plain,
% 7.52/1.49      ( k11_relat_1(sK3,sK1) != k2_relat_1(sK3)
% 7.52/1.49      | k11_relat_1(sK3,sK1) = k1_xboole_0 ),
% 7.52/1.49      inference(superposition,[status(thm)],[c_1629,c_1085]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_7,plain,
% 7.52/1.49      ( ~ v1_relat_1(X0)
% 7.52/1.49      | k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
% 7.52/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_368,plain,
% 7.52/1.49      ( k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1)
% 7.52/1.49      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
% 7.52/1.49      | sK3 != X0 ),
% 7.52/1.49      inference(resolution_lifted,[status(thm)],[c_7,c_332]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_369,plain,
% 7.52/1.49      ( k9_relat_1(sK3,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK3,X0)
% 7.52/1.49      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
% 7.52/1.49      inference(unflattening,[status(thm)],[c_368]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_509,plain,
% 7.52/1.49      ( k9_relat_1(sK3,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK3,X0)
% 7.52/1.49      | ~ sP3_iProver_split ),
% 7.52/1.49      inference(splitting,
% 7.52/1.49                [splitting(split),new_symbols(definition,[sP3_iProver_split])],
% 7.52/1.49                [c_369]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_827,plain,
% 7.52/1.49      ( k9_relat_1(sK3,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK3,X0)
% 7.52/1.49      | sP3_iProver_split != iProver_top ),
% 7.52/1.49      inference(predicate_to_equality,[status(thm)],[c_509]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_510,plain,
% 7.52/1.49      ( sP3_iProver_split | sP0_iProver_split ),
% 7.52/1.49      inference(splitting,
% 7.52/1.49                [splitting(split),new_symbols(definition,[])],
% 7.52/1.49                [c_369]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_1437,plain,
% 7.52/1.49      ( k9_relat_1(sK3,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK3,X0) ),
% 7.52/1.49      inference(global_propositional_subsumption,
% 7.52/1.49                [status(thm)],
% 7.52/1.49                [c_827,c_510,c_509,c_912,c_963]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_14,plain,
% 7.52/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.52/1.49      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 7.52/1.49      inference(cnf_transformation,[],[f55]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_313,plain,
% 7.52/1.49      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 7.52/1.49      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 7.52/1.49      | sK3 != X2 ),
% 7.52/1.49      inference(resolution_lifted,[status(thm)],[c_14,c_20]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_314,plain,
% 7.52/1.49      ( k7_relset_1(X0,X1,sK3,X2) = k9_relat_1(sK3,X2)
% 7.52/1.49      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 7.52/1.49      inference(unflattening,[status(thm)],[c_313]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_931,plain,
% 7.52/1.49      ( k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3,X0) = k9_relat_1(sK3,X0) ),
% 7.52/1.49      inference(equality_resolution,[status(thm)],[c_314]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_16,plain,
% 7.52/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.52/1.49      | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
% 7.52/1.49      inference(cnf_transformation,[],[f56]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_295,plain,
% 7.52/1.49      ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
% 7.52/1.49      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 7.52/1.49      | sK3 != X2 ),
% 7.52/1.49      inference(resolution_lifted,[status(thm)],[c_16,c_20]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_296,plain,
% 7.52/1.49      ( k7_relset_1(X0,X1,sK3,X0) = k2_relset_1(X0,X1,sK3)
% 7.52/1.49      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 7.52/1.49      inference(unflattening,[status(thm)],[c_295]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_988,plain,
% 7.52/1.49      ( k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3,k2_enumset1(sK1,sK1,sK1,sK1)) = k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) ),
% 7.52/1.49      inference(equality_resolution,[status(thm)],[c_296]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_989,plain,
% 7.52/1.49      ( k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3,k2_enumset1(sK1,sK1,sK1,sK1)) = k2_relat_1(sK3) ),
% 7.52/1.49      inference(light_normalisation,[status(thm)],[c_988,c_930]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_1440,plain,
% 7.52/1.49      ( k9_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1)) = k2_relat_1(sK3) ),
% 7.52/1.49      inference(superposition,[status(thm)],[c_931,c_989]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_1499,plain,
% 7.52/1.49      ( k11_relat_1(sK3,sK1) = k2_relat_1(sK3) ),
% 7.52/1.49      inference(superposition,[status(thm)],[c_1437,c_1440]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_2021,plain,
% 7.52/1.49      ( k11_relat_1(sK3,sK1) = k1_xboole_0
% 7.52/1.49      | k2_relat_1(sK3) != k2_relat_1(sK3) ),
% 7.52/1.49      inference(light_normalisation,[status(thm)],[c_2019,c_1499]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_2022,plain,
% 7.52/1.49      ( k11_relat_1(sK3,sK1) = k1_xboole_0 ),
% 7.52/1.49      inference(equality_resolution_simp,[status(thm)],[c_2021]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_2216,plain,
% 7.52/1.49      ( k2_relat_1(sK3) = k1_xboole_0 ),
% 7.52/1.49      inference(demodulation,[status(thm)],[c_2022,c_1499]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_4,plain,
% 7.52/1.49      ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) ),
% 7.52/1.49      inference(cnf_transformation,[],[f78]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_836,plain,
% 7.52/1.49      ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) = iProver_top ),
% 7.52/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_17,plain,
% 7.52/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.52/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.52/1.49      | ~ r2_hidden(X3,X1)
% 7.52/1.49      | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
% 7.52/1.49      | ~ v1_funct_1(X0)
% 7.52/1.49      | k1_xboole_0 = X2 ),
% 7.52/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_21,negated_conjecture,
% 7.52/1.49      ( v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
% 7.52/1.49      inference(cnf_transformation,[],[f76]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_255,plain,
% 7.52/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.52/1.49      | ~ r2_hidden(X3,X1)
% 7.52/1.49      | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
% 7.52/1.49      | ~ v1_funct_1(X0)
% 7.52/1.49      | k2_enumset1(sK1,sK1,sK1,sK1) != X1
% 7.52/1.49      | sK2 != X2
% 7.52/1.49      | sK3 != X0
% 7.52/1.49      | k1_xboole_0 = X2 ),
% 7.52/1.49      inference(resolution_lifted,[status(thm)],[c_17,c_21]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_256,plain,
% 7.52/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))
% 7.52/1.49      | ~ r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1))
% 7.52/1.49      | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3))
% 7.52/1.49      | ~ v1_funct_1(sK3)
% 7.52/1.49      | k1_xboole_0 = sK2 ),
% 7.52/1.49      inference(unflattening,[status(thm)],[c_255]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_19,negated_conjecture,
% 7.52/1.49      ( k1_xboole_0 != sK2 ),
% 7.52/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_260,plain,
% 7.52/1.49      ( ~ r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1))
% 7.52/1.49      | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3)) ),
% 7.52/1.49      inference(global_propositional_subsumption,
% 7.52/1.49                [status(thm)],
% 7.52/1.49                [c_256,c_22,c_20,c_19]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_832,plain,
% 7.52/1.49      ( r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top
% 7.52/1.49      | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3)) = iProver_top ),
% 7.52/1.49      inference(predicate_to_equality,[status(thm)],[c_260]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_1321,plain,
% 7.52/1.49      ( r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top
% 7.52/1.49      | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) = iProver_top ),
% 7.52/1.49      inference(light_normalisation,[status(thm)],[c_832,c_930]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_1325,plain,
% 7.52/1.49      ( r2_hidden(k1_funct_1(sK3,sK1),k2_relat_1(sK3)) = iProver_top ),
% 7.52/1.49      inference(superposition,[status(thm)],[c_836,c_1321]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_7476,plain,
% 7.52/1.49      ( r2_hidden(k1_funct_1(sK3,sK1),k1_xboole_0) = iProver_top ),
% 7.52/1.49      inference(demodulation,[status(thm)],[c_2216,c_1325]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_7483,plain,
% 7.52/1.49      ( r2_hidden(k1_funct_1(sK3,sK1),k1_xboole_0) ),
% 7.52/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_7476]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(contradiction,plain,
% 7.52/1.49      ( $false ),
% 7.52/1.49      inference(minisat,[status(thm)],[c_14887,c_7483]) ).
% 7.52/1.49  
% 7.52/1.49  
% 7.52/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.52/1.49  
% 7.52/1.49  ------                               Statistics
% 7.52/1.49  
% 7.52/1.49  ------ General
% 7.52/1.49  
% 7.52/1.49  abstr_ref_over_cycles:                  0
% 7.52/1.49  abstr_ref_under_cycles:                 0
% 7.52/1.49  gc_basic_clause_elim:                   0
% 7.52/1.49  forced_gc_time:                         0
% 7.52/1.49  parsing_time:                           0.011
% 7.52/1.49  unif_index_cands_time:                  0.
% 7.52/1.49  unif_index_add_time:                    0.
% 7.52/1.49  orderings_time:                         0.
% 7.52/1.49  out_proof_time:                         0.011
% 7.52/1.49  total_time:                             0.961
% 7.52/1.49  num_of_symbols:                         59
% 7.52/1.49  num_of_terms:                           18847
% 7.52/1.49  
% 7.52/1.49  ------ Preprocessing
% 7.52/1.49  
% 7.52/1.49  num_of_splits:                          8
% 7.52/1.49  num_of_split_atoms:                     5
% 7.52/1.49  num_of_reused_defs:                     3
% 7.52/1.49  num_eq_ax_congr_red:                    45
% 7.52/1.49  num_of_sem_filtered_clauses:            1
% 7.52/1.49  num_of_subtypes:                        0
% 7.52/1.49  monotx_restored_types:                  0
% 7.52/1.49  sat_num_of_epr_types:                   0
% 7.52/1.49  sat_num_of_non_cyclic_types:            0
% 7.52/1.49  sat_guarded_non_collapsed_types:        0
% 7.52/1.49  num_pure_diseq_elim:                    0
% 7.52/1.49  simp_replaced_by:                       0
% 7.52/1.49  res_preprocessed:                       118
% 7.52/1.49  prep_upred:                             0
% 7.52/1.49  prep_unflattend:                        14
% 7.52/1.49  smt_new_axioms:                         0
% 7.52/1.49  pred_elim_cands:                        1
% 7.52/1.49  pred_elim:                              5
% 7.52/1.49  pred_elim_cl:                           5
% 7.52/1.49  pred_elim_cycles:                       7
% 7.52/1.49  merged_defs:                            0
% 7.52/1.49  merged_defs_ncl:                        0
% 7.52/1.49  bin_hyper_res:                          0
% 7.52/1.49  prep_cycles:                            4
% 7.52/1.49  pred_elim_time:                         0.005
% 7.52/1.49  splitting_time:                         0.
% 7.52/1.49  sem_filter_time:                        0.
% 7.52/1.49  monotx_time:                            0.
% 7.52/1.49  subtype_inf_time:                       0.
% 7.52/1.49  
% 7.52/1.49  ------ Problem properties
% 7.52/1.49  
% 7.52/1.49  clauses:                                26
% 7.52/1.49  conjectures:                            2
% 7.52/1.49  epr:                                    6
% 7.52/1.49  horn:                                   19
% 7.52/1.49  ground:                                 6
% 7.52/1.49  unary:                                  5
% 7.52/1.49  binary:                                 14
% 7.52/1.49  lits:                                   55
% 7.52/1.49  lits_eq:                                27
% 7.52/1.49  fd_pure:                                0
% 7.52/1.49  fd_pseudo:                              0
% 7.52/1.49  fd_cond:                                0
% 7.52/1.49  fd_pseudo_cond:                         3
% 7.52/1.49  ac_symbols:                             0
% 7.52/1.49  
% 7.52/1.49  ------ Propositional Solver
% 7.52/1.49  
% 7.52/1.49  prop_solver_calls:                      31
% 7.52/1.49  prop_fast_solver_calls:                 1438
% 7.52/1.49  smt_solver_calls:                       0
% 7.52/1.49  smt_fast_solver_calls:                  0
% 7.52/1.49  prop_num_of_clauses:                    6383
% 7.52/1.49  prop_preprocess_simplified:             13007
% 7.52/1.49  prop_fo_subsumed:                       35
% 7.52/1.49  prop_solver_time:                       0.
% 7.52/1.49  smt_solver_time:                        0.
% 7.52/1.49  smt_fast_solver_time:                   0.
% 7.52/1.49  prop_fast_solver_time:                  0.
% 7.52/1.49  prop_unsat_core_time:                   0.
% 7.52/1.49  
% 7.52/1.49  ------ QBF
% 7.52/1.49  
% 7.52/1.49  qbf_q_res:                              0
% 7.52/1.49  qbf_num_tautologies:                    0
% 7.52/1.49  qbf_prep_cycles:                        0
% 7.52/1.49  
% 7.52/1.49  ------ BMC1
% 7.52/1.49  
% 7.52/1.49  bmc1_current_bound:                     -1
% 7.52/1.49  bmc1_last_solved_bound:                 -1
% 7.52/1.49  bmc1_unsat_core_size:                   -1
% 7.52/1.49  bmc1_unsat_core_parents_size:           -1
% 7.52/1.49  bmc1_merge_next_fun:                    0
% 7.52/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.52/1.49  
% 7.52/1.49  ------ Instantiation
% 7.52/1.49  
% 7.52/1.49  inst_num_of_clauses:                    1537
% 7.52/1.49  inst_num_in_passive:                    767
% 7.52/1.49  inst_num_in_active:                     503
% 7.52/1.49  inst_num_in_unprocessed:                266
% 7.52/1.49  inst_num_of_loops:                      743
% 7.52/1.49  inst_num_of_learning_restarts:          0
% 7.52/1.49  inst_num_moves_active_passive:          236
% 7.52/1.49  inst_lit_activity:                      0
% 7.52/1.49  inst_lit_activity_moves:                0
% 7.52/1.49  inst_num_tautologies:                   0
% 7.52/1.49  inst_num_prop_implied:                  0
% 7.52/1.49  inst_num_existing_simplified:           0
% 7.52/1.49  inst_num_eq_res_simplified:             0
% 7.52/1.49  inst_num_child_elim:                    0
% 7.52/1.49  inst_num_of_dismatching_blockings:      1237
% 7.52/1.49  inst_num_of_non_proper_insts:           2167
% 7.52/1.49  inst_num_of_duplicates:                 0
% 7.52/1.49  inst_inst_num_from_inst_to_res:         0
% 7.52/1.49  inst_dismatching_checking_time:         0.
% 7.52/1.49  
% 7.52/1.49  ------ Resolution
% 7.52/1.49  
% 7.52/1.49  res_num_of_clauses:                     0
% 7.52/1.49  res_num_in_passive:                     0
% 7.52/1.49  res_num_in_active:                      0
% 7.52/1.49  res_num_of_loops:                       122
% 7.52/1.49  res_forward_subset_subsumed:            310
% 7.52/1.49  res_backward_subset_subsumed:           0
% 7.52/1.49  res_forward_subsumed:                   0
% 7.52/1.49  res_backward_subsumed:                  0
% 7.52/1.49  res_forward_subsumption_resolution:     0
% 7.52/1.49  res_backward_subsumption_resolution:    0
% 7.52/1.49  res_clause_to_clause_subsumption:       27055
% 7.52/1.49  res_orphan_elimination:                 0
% 7.52/1.49  res_tautology_del:                      112
% 7.52/1.49  res_num_eq_res_simplified:              0
% 7.52/1.49  res_num_sel_changes:                    0
% 7.52/1.49  res_moves_from_active_to_pass:          0
% 7.52/1.49  
% 7.52/1.49  ------ Superposition
% 7.52/1.49  
% 7.52/1.49  sup_time_total:                         0.
% 7.52/1.49  sup_time_generating:                    0.
% 7.52/1.49  sup_time_sim_full:                      0.
% 7.52/1.49  sup_time_sim_immed:                     0.
% 7.52/1.49  
% 7.52/1.49  sup_num_of_clauses:                     1662
% 7.52/1.49  sup_num_in_active:                      136
% 7.52/1.49  sup_num_in_passive:                     1526
% 7.52/1.49  sup_num_of_loops:                       148
% 7.52/1.49  sup_fw_superposition:                   1065
% 7.52/1.49  sup_bw_superposition:                   1588
% 7.52/1.49  sup_immediate_simplified:               502
% 7.52/1.49  sup_given_eliminated:                   0
% 7.52/1.49  comparisons_done:                       0
% 7.52/1.49  comparisons_avoided:                    569
% 7.52/1.49  
% 7.52/1.49  ------ Simplifications
% 7.52/1.49  
% 7.52/1.49  
% 7.52/1.49  sim_fw_subset_subsumed:                 76
% 7.52/1.49  sim_bw_subset_subsumed:                 7
% 7.52/1.49  sim_fw_subsumed:                        371
% 7.52/1.49  sim_bw_subsumed:                        36
% 7.52/1.49  sim_fw_subsumption_res:                 0
% 7.52/1.49  sim_bw_subsumption_res:                 0
% 7.52/1.49  sim_tautology_del:                      52
% 7.52/1.49  sim_eq_tautology_del:                   10
% 7.52/1.49  sim_eq_res_simp:                        10
% 7.52/1.49  sim_fw_demodulated:                     4
% 7.52/1.49  sim_bw_demodulated:                     9
% 7.52/1.49  sim_light_normalised:                   44
% 7.52/1.49  sim_joinable_taut:                      0
% 7.52/1.49  sim_joinable_simp:                      0
% 7.52/1.49  sim_ac_normalised:                      0
% 7.52/1.49  sim_smt_subsumption:                    0
% 7.52/1.49  
%------------------------------------------------------------------------------
