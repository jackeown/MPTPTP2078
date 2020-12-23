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
% DateTime   : Thu Dec  3 12:05:20 EST 2020

% Result     : Theorem 4.12s
% Output     : CNFRefutation 4.12s
% Verified   : 
% Statistics : Number of formulae       :  233 (5695 expanded)
%              Number of clauses        :  153 (1509 expanded)
%              Number of leaves         :   24 (1346 expanded)
%              Depth                    :   29
%              Number of atoms          :  603 (15708 expanded)
%              Number of equality atoms :  331 (7262 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f39])).

fof(f43,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X5)) = X5
        & r2_hidden(sK2(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK1(X0,X1)) = X2
        & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK0(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK0(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK0(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK0(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK1(X0,X1)) = sK0(X0,X1)
                  & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK0(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK2(X0,X5)) = X5
                    & r2_hidden(sK2(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f40,f43,f42,f41])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(sK1(X0,X1),k1_relat_1(X0))
      | r2_hidden(sK0(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

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

fof(f36,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f37,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f45,plain,
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

fof(f46,plain,
    ( k1_tarski(k1_funct_1(sK5,sK3)) != k2_relset_1(k1_tarski(sK3),sK4,sK5)
    & k1_xboole_0 != sK4
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4)))
    & v1_funct_2(sK5,k1_tarski(sK3),sK4)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f37,f45])).

fof(f73,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f46])).

fof(f75,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4))) ),
    inference(cnf_transformation,[],[f46])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f78,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f50,f51])).

fof(f79,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f49,f78])).

fof(f84,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) ),
    inference(definition_unfolding,[],[f75,f79])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k1_relat_1(X1))
          | k1_xboole_0 = k11_relat_1(X1,X0) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X1))
      | k1_xboole_0 = k11_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f66,f79])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f55,f79])).

fof(f1,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f48,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f59,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f77,plain,(
    k1_tarski(k1_funct_1(sK5,sK3)) != k2_relset_1(k1_tarski(sK3),sK4,sK5) ),
    inference(cnf_transformation,[],[f46])).

fof(f83,plain,(
    k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) ),
    inference(definition_unfolding,[],[f77,f79,f79])).

fof(f62,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f86,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f87,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f86])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f34])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f74,plain,(
    v1_funct_2(sK5,k1_tarski(sK3),sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f85,plain,(
    v1_funct_2(sK5,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
    inference(definition_unfolding,[],[f74,f79])).

fof(f76,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f46])).

fof(f6,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f80,plain,(
    ! [X0] : ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
    inference(definition_unfolding,[],[f52,f79])).

fof(f60,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK2(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f89,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK2(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f60])).

cnf(c_12,plain,
    ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
    | r2_hidden(sK0(X0,X1),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_316,plain,
    ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
    | r2_hidden(sK0(X0,X1),X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_27])).

cnf(c_317,plain,
    ( r2_hidden(sK1(sK5,X0),k1_relat_1(sK5))
    | r2_hidden(sK0(sK5,X0),X0)
    | ~ v1_relat_1(sK5)
    | k2_relat_1(sK5) = X0 ),
    inference(unflattening,[status(thm)],[c_316])).

cnf(c_1348,plain,
    ( k2_relat_1(sK5) = X0
    | r2_hidden(sK1(sK5,X0),k1_relat_1(sK5)) = iProver_top
    | r2_hidden(sK0(sK5,X0),X0) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_317])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_30,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_318,plain,
    ( k2_relat_1(sK5) = X0
    | r2_hidden(sK1(sK5,X0),k1_relat_1(sK5)) = iProver_top
    | r2_hidden(sK0(sK5,X0),X0) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_317])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1445,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1446,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1445])).

cnf(c_3262,plain,
    ( r2_hidden(sK0(sK5,X0),X0) = iProver_top
    | r2_hidden(sK1(sK5,X0),k1_relat_1(sK5)) = iProver_top
    | k2_relat_1(sK5) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1348,c_30,c_318,c_1446])).

cnf(c_3263,plain,
    ( k2_relat_1(sK5) = X0
    | r2_hidden(sK1(sK5,X0),k1_relat_1(sK5)) = iProver_top
    | r2_hidden(sK0(sK5,X0),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_3262])).

cnf(c_9,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_6,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k11_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1357,plain,
    ( k11_relat_1(X0,X1) = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_352,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_27])).

cnf(c_353,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK5))
    | ~ v1_relat_1(sK5)
    | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k11_relat_1(sK5,X0) ),
    inference(unflattening,[status(thm)],[c_352])).

cnf(c_1346,plain,
    ( k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k11_relat_1(sK5,X0)
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_353])).

cnf(c_1794,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK5))
    | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k11_relat_1(sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_353,c_25,c_1445])).

cnf(c_1796,plain,
    ( k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k11_relat_1(sK5,X0)
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1794])).

cnf(c_2666,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k11_relat_1(sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1346,c_1796])).

cnf(c_2667,plain,
    ( k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k11_relat_1(sK5,X0)
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2666])).

cnf(c_2670,plain,
    ( k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k11_relat_1(sK5,X0)
    | k11_relat_1(sK5,X0) = k1_xboole_0
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1357,c_2667])).

cnf(c_2672,plain,
    ( ~ v1_relat_1(sK5)
    | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k11_relat_1(sK5,X0)
    | k11_relat_1(sK5,X0) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2670])).

cnf(c_3890,plain,
    ( k11_relat_1(sK5,X0) = k1_xboole_0
    | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k11_relat_1(sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2670,c_25,c_1445,c_2672])).

cnf(c_3891,plain,
    ( k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k11_relat_1(sK5,X0)
    | k11_relat_1(sK5,X0) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_3890])).

cnf(c_3,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1360,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1355,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1684,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1360,c_1355])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1358,plain,
    ( k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2274,plain,
    ( k9_relat_1(k1_xboole_0,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_1684,c_1358])).

cnf(c_3894,plain,
    ( k9_relat_1(k1_xboole_0,k11_relat_1(sK5,X0)) = k11_relat_1(k1_xboole_0,k1_funct_1(sK5,X0))
    | k11_relat_1(sK5,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3891,c_2274])).

cnf(c_0,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_283,plain,
    ( k1_xboole_0 = X0
    | o_0_0_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1])).

cnf(c_284,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(unflattening,[status(thm)],[c_283])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1353,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2043,plain,
    ( k7_relset_1(X0,X1,k1_xboole_0,X2) = k9_relat_1(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_1360,c_1353])).

cnf(c_2588,plain,
    ( k7_relset_1(X0,X1,o_0_0_xboole_0,X2) = k9_relat_1(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_284,c_2043])).

cnf(c_1601,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_284,c_1360])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1351,plain,
    ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2513,plain,
    ( k7_relset_1(X0,X1,o_0_0_xboole_0,X0) = k2_relset_1(X0,X1,o_0_0_xboole_0) ),
    inference(superposition,[status(thm)],[c_1601,c_1351])).

cnf(c_4964,plain,
    ( k2_relset_1(X0,X1,o_0_0_xboole_0) = k9_relat_1(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_2588,c_2513])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1354,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2515,plain,
    ( k2_relset_1(X0,X1,o_0_0_xboole_0) = k2_relat_1(o_0_0_xboole_0) ),
    inference(superposition,[status(thm)],[c_1601,c_1354])).

cnf(c_6929,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k2_relat_1(o_0_0_xboole_0) ),
    inference(superposition,[status(thm)],[c_4964,c_2515])).

cnf(c_8324,plain,
    ( k11_relat_1(sK5,X0) = k1_xboole_0
    | k11_relat_1(k1_xboole_0,k1_funct_1(sK5,X0)) = k2_relat_1(o_0_0_xboole_0) ),
    inference(superposition,[status(thm)],[c_3894,c_6929])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k11_relat_1(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1356,plain,
    ( k11_relat_1(X0,X1) != k1_xboole_0
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_9585,plain,
    ( k11_relat_1(sK5,X0) = k1_xboole_0
    | k2_relat_1(o_0_0_xboole_0) != k1_xboole_0
    | r2_hidden(k1_funct_1(sK5,X0),k1_relat_1(k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8324,c_1356])).

cnf(c_8,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1410,plain,
    ( k2_relat_1(o_0_0_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_284,c_8])).

cnf(c_1435,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1437,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1435])).

cnf(c_1436,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1441,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1436])).

cnf(c_10087,plain,
    ( r2_hidden(k1_funct_1(sK5,X0),k1_relat_1(k1_xboole_0)) != iProver_top
    | k11_relat_1(sK5,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9585,c_1410,c_1437,c_1441])).

cnf(c_10088,plain,
    ( k11_relat_1(sK5,X0) = k1_xboole_0
    | r2_hidden(k1_funct_1(sK5,X0),k1_relat_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_10087])).

cnf(c_10097,plain,
    ( k11_relat_1(sK5,X0) = k1_xboole_0
    | r2_hidden(k1_funct_1(sK5,X0),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_10088])).

cnf(c_1584,plain,
    ( r2_hidden(X0,k1_relat_1(sK5))
    | ~ v1_relat_1(sK5)
    | k11_relat_1(sK5,X0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1585,plain,
    ( k11_relat_1(sK5,X0) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1584])).

cnf(c_1350,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1685,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1350,c_1355])).

cnf(c_2408,plain,
    ( k9_relat_1(sK5,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK5,X0) ),
    inference(superposition,[status(thm)],[c_1685,c_1358])).

cnf(c_2044,plain,
    ( k7_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5,X0) = k9_relat_1(sK5,X0) ),
    inference(superposition,[status(thm)],[c_1350,c_1353])).

cnf(c_2105,plain,
    ( k7_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5,k2_enumset1(sK3,sK3,sK3,sK3)) = k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) ),
    inference(superposition,[status(thm)],[c_1350,c_1351])).

cnf(c_3887,plain,
    ( k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k9_relat_1(sK5,k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(superposition,[status(thm)],[c_2044,c_2105])).

cnf(c_1767,plain,
    ( k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1350,c_1354])).

cnf(c_8024,plain,
    ( k9_relat_1(sK5,k2_enumset1(sK3,sK3,sK3,sK3)) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_3887,c_1767])).

cnf(c_8109,plain,
    ( k11_relat_1(sK5,sK3) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_2408,c_8024])).

cnf(c_23,negated_conjecture,
    ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_3896,plain,
    ( k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) != k11_relat_1(sK5,sK3)
    | k11_relat_1(sK5,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3891,c_23])).

cnf(c_8022,plain,
    ( k9_relat_1(sK5,k2_enumset1(sK3,sK3,sK3,sK3)) != k11_relat_1(sK5,sK3)
    | k11_relat_1(sK5,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3887,c_3896])).

cnf(c_1573,plain,
    ( ~ v1_relat_1(sK5)
    | k9_relat_1(sK5,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK5,X0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1580,plain,
    ( ~ v1_relat_1(sK5)
    | k9_relat_1(sK5,k2_enumset1(sK3,sK3,sK3,sK3)) = k11_relat_1(sK5,sK3) ),
    inference(instantiation,[status(thm)],[c_1573])).

cnf(c_968,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1595,plain,
    ( X0 != X1
    | k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != X1
    | k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) = X0 ),
    inference(instantiation,[status(thm)],[c_968])).

cnf(c_2144,plain,
    ( X0 != k11_relat_1(sK5,sK3)
    | k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) = X0
    | k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k11_relat_1(sK5,sK3) ),
    inference(instantiation,[status(thm)],[c_1595])).

cnf(c_2661,plain,
    ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) = k9_relat_1(sK5,k2_enumset1(sK3,sK3,sK3,sK3))
    | k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k11_relat_1(sK5,sK3)
    | k9_relat_1(sK5,k2_enumset1(sK3,sK3,sK3,sK3)) != k11_relat_1(sK5,sK3) ),
    inference(instantiation,[status(thm)],[c_2144])).

cnf(c_2673,plain,
    ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) = k11_relat_1(sK5,sK3)
    | k11_relat_1(sK5,sK3) = k1_xboole_0
    | v1_relat_1(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2670])).

cnf(c_1485,plain,
    ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != X0
    | k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) = k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5)
    | k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) != X0 ),
    inference(instantiation,[status(thm)],[c_968])).

cnf(c_4957,plain,
    ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) = k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5)
    | k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k9_relat_1(sK5,k2_enumset1(sK3,sK3,sK3,sK3))
    | k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) != k9_relat_1(sK5,k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_1485])).

cnf(c_8028,plain,
    ( k11_relat_1(sK5,sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8022,c_25,c_30,c_23,c_1445,c_1446,c_1580,c_2661,c_2673,c_3887,c_4957])).

cnf(c_8154,plain,
    ( k2_relat_1(sK5) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8109,c_8028])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_397,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_27])).

cnf(c_398,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK5))
    | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5))
    | ~ v1_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_397])).

cnf(c_1343,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_398])).

cnf(c_1498,plain,
    ( r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5))
    | ~ r2_hidden(X0,k1_relat_1(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_398,c_25,c_1445])).

cnf(c_1499,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK5))
    | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) ),
    inference(renaming,[status(thm)],[c_1498])).

cnf(c_1500,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1499])).

cnf(c_1930,plain,
    ( r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1343,c_1500])).

cnf(c_1931,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) = iProver_top ),
    inference(renaming,[status(thm)],[c_1930])).

cnf(c_9477,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_8154,c_1931])).

cnf(c_10106,plain,
    ( k11_relat_1(sK5,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10097,c_30,c_1446,c_1585,c_9477])).

cnf(c_10109,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_10106,c_1356])).

cnf(c_1583,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK5))
    | ~ v1_relat_1(sK5)
    | k11_relat_1(sK5,X0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1589,plain,
    ( k11_relat_1(sK5,X0) != k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1583])).

cnf(c_10209,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10109,c_30,c_1446,c_1585,c_1589,c_9477,c_10097])).

cnf(c_10214,plain,
    ( k2_relat_1(sK5) = X0
    | r2_hidden(sK0(sK5,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3263,c_10209])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK5,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_295,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k1_funct_1(X2,X0),k2_relset_1(X1,X3,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X2)
    | k2_enumset1(sK3,sK3,sK3,sK3) != X1
    | sK4 != X3
    | sK5 != X2
    | k1_xboole_0 = X3 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_26])).

cnf(c_296,plain,
    ( ~ r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3))
    | r2_hidden(k1_funct_1(sK5,X0),k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))
    | ~ v1_funct_1(sK5)
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_295])).

cnf(c_24,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_300,plain,
    ( r2_hidden(k1_funct_1(sK5,X0),k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5))
    | ~ r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_296,c_27,c_25,c_24])).

cnf(c_301,plain,
    ( ~ r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3))
    | r2_hidden(k1_funct_1(sK5,X0),k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5)) ),
    inference(renaming,[status(thm)],[c_300])).

cnf(c_1349,plain,
    ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_301])).

cnf(c_3548,plain,
    ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1767,c_1349])).

cnf(c_10756,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) = k2_relat_1(sK5)
    | r2_hidden(k1_funct_1(sK5,sK0(sK5,k2_enumset1(sK3,sK3,sK3,sK3))),k2_relat_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10214,c_3548])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_288,plain,
    ( k2_enumset1(X0,X0,X0,X0) != o_0_0_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_2])).

cnf(c_289,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_288])).

cnf(c_967,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2069,plain,
    ( o_0_0_xboole_0 = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_967])).

cnf(c_1724,plain,
    ( X0 != X1
    | o_0_0_xboole_0 != X1
    | o_0_0_xboole_0 = X0 ),
    inference(instantiation,[status(thm)],[c_968])).

cnf(c_2068,plain,
    ( X0 != o_0_0_xboole_0
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1724])).

cnf(c_3518,plain,
    ( k2_relat_1(sK5) != o_0_0_xboole_0
    | o_0_0_xboole_0 = k2_relat_1(sK5)
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2068])).

cnf(c_3268,plain,
    ( k2_enumset1(k1_funct_1(sK5,sK1(sK5,X0)),k1_funct_1(sK5,sK1(sK5,X0)),k1_funct_1(sK5,sK1(sK5,X0)),k1_funct_1(sK5,sK1(sK5,X0))) = k11_relat_1(sK5,sK1(sK5,X0))
    | k2_relat_1(sK5) = X0
    | r2_hidden(sK0(sK5,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3263,c_2667])).

cnf(c_2104,plain,
    ( k7_relset_1(X0,X1,k1_xboole_0,X0) = k2_relset_1(X0,X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1360,c_1351])).

cnf(c_2756,plain,
    ( k2_relset_1(X0,X1,k1_xboole_0) = k9_relat_1(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_2104,c_2043])).

cnf(c_1766,plain,
    ( k2_relset_1(X0,X1,k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1360,c_1354])).

cnf(c_5124,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2756,c_1766])).

cnf(c_5129,plain,
    ( k11_relat_1(k1_xboole_0,X0) = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5124,c_2274])).

cnf(c_5364,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5129,c_1356])).

cnf(c_5680,plain,
    ( r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5364,c_8,c_1437,c_1441])).

cnf(c_5689,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_5680])).

cnf(c_5706,plain,
    ( r2_hidden(X0,o_0_0_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_284,c_5689])).

cnf(c_7468,plain,
    ( k2_enumset1(k1_funct_1(sK5,sK1(sK5,o_0_0_xboole_0)),k1_funct_1(sK5,sK1(sK5,o_0_0_xboole_0)),k1_funct_1(sK5,sK1(sK5,o_0_0_xboole_0)),k1_funct_1(sK5,sK1(sK5,o_0_0_xboole_0))) = k11_relat_1(sK5,sK1(sK5,o_0_0_xboole_0))
    | k2_relat_1(sK5) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_3268,c_5706])).

cnf(c_8767,plain,
    ( k11_relat_1(sK5,sK1(sK5,o_0_0_xboole_0)) != o_0_0_xboole_0
    | k2_relat_1(sK5) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_7468,c_288])).

cnf(c_10122,plain,
    ( k2_relat_1(sK5) = o_0_0_xboole_0
    | k1_xboole_0 != o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_10106,c_8767])).

cnf(c_1489,plain,
    ( k2_enumset1(X0,X0,X0,X0) != X1
    | k2_enumset1(X0,X0,X0,X0) = o_0_0_xboole_0
    | o_0_0_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_968])).

cnf(c_10607,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k2_relat_1(sK5)
    | k2_enumset1(X0,X0,X0,X0) = o_0_0_xboole_0
    | o_0_0_xboole_0 != k2_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1489])).

cnf(c_10608,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) != k2_relat_1(sK5)
    | k2_enumset1(sK3,sK3,sK3,sK3) = o_0_0_xboole_0
    | o_0_0_xboole_0 != k2_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_10607])).

cnf(c_10897,plain,
    ( r2_hidden(k1_funct_1(sK5,sK0(sK5,k2_enumset1(sK3,sK3,sK3,sK3))),k2_relat_1(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10756,c_284,c_289,c_2069,c_3518,c_10122,c_10608])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK2(X1,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_367,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK2(X1,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_27])).

cnf(c_368,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK5))
    | r2_hidden(sK2(sK5,X0),k1_relat_1(sK5))
    | ~ v1_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_367])).

cnf(c_1345,plain,
    ( r2_hidden(X0,k2_relat_1(sK5)) != iProver_top
    | r2_hidden(sK2(sK5,X0),k1_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_368])).

cnf(c_1473,plain,
    ( r2_hidden(sK2(sK5,X0),k1_relat_1(sK5))
    | ~ r2_hidden(X0,k2_relat_1(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_368,c_25,c_1445])).

cnf(c_1474,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK5))
    | r2_hidden(sK2(sK5,X0),k1_relat_1(sK5)) ),
    inference(renaming,[status(thm)],[c_1473])).

cnf(c_1475,plain,
    ( r2_hidden(X0,k2_relat_1(sK5)) != iProver_top
    | r2_hidden(sK2(sK5,X0),k1_relat_1(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1474])).

cnf(c_2411,plain,
    ( r2_hidden(sK2(sK5,X0),k1_relat_1(sK5)) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1345,c_1475])).

cnf(c_2412,plain,
    ( r2_hidden(X0,k2_relat_1(sK5)) != iProver_top
    | r2_hidden(sK2(sK5,X0),k1_relat_1(sK5)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2411])).

cnf(c_10219,plain,
    ( r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2412,c_10209])).

cnf(c_10906,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_10897,c_10219])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:03:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 4.12/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.12/0.99  
% 4.12/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.12/0.99  
% 4.12/0.99  ------  iProver source info
% 4.12/0.99  
% 4.12/0.99  git: date: 2020-06-30 10:37:57 +0100
% 4.12/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.12/0.99  git: non_committed_changes: false
% 4.12/0.99  git: last_make_outside_of_git: false
% 4.12/0.99  
% 4.12/0.99  ------ 
% 4.12/0.99  ------ Parsing...
% 4.12/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.12/0.99  
% 4.12/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 4.12/0.99  
% 4.12/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.12/0.99  
% 4.12/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.12/0.99  ------ Proving...
% 4.12/0.99  ------ Problem Properties 
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  clauses                                 25
% 4.12/0.99  conjectures                             3
% 4.12/0.99  EPR                                     2
% 4.12/0.99  Horn                                    22
% 4.12/0.99  unary                                   8
% 4.12/0.99  binary                                  7
% 4.12/0.99  lits                                    56
% 4.12/0.99  lits eq                                 20
% 4.12/0.99  fd_pure                                 0
% 4.12/0.99  fd_pseudo                               0
% 4.12/0.99  fd_cond                                 3
% 4.12/0.99  fd_pseudo_cond                          0
% 4.12/0.99  AC symbols                              0
% 4.12/0.99  
% 4.12/0.99  ------ Input Options Time Limit: Unbounded
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  ------ 
% 4.12/0.99  Current options:
% 4.12/0.99  ------ 
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  ------ Proving...
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  % SZS status Theorem for theBenchmark.p
% 4.12/0.99  
% 4.12/0.99   Resolution empty clause
% 4.12/0.99  
% 4.12/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 4.12/0.99  
% 4.12/0.99  fof(f12,axiom,(
% 4.12/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 4.12/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.12/0.99  
% 4.12/0.99  fof(f26,plain,(
% 4.12/0.99    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 4.12/0.99    inference(ennf_transformation,[],[f12])).
% 4.12/0.99  
% 4.12/0.99  fof(f27,plain,(
% 4.12/0.99    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.12/0.99    inference(flattening,[],[f26])).
% 4.12/0.99  
% 4.12/0.99  fof(f39,plain,(
% 4.12/0.99    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.12/0.99    inference(nnf_transformation,[],[f27])).
% 4.12/0.99  
% 4.12/0.99  fof(f40,plain,(
% 4.12/0.99    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.12/0.99    inference(rectify,[],[f39])).
% 4.12/0.99  
% 4.12/0.99  fof(f43,plain,(
% 4.12/0.99    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X5)) = X5 & r2_hidden(sK2(X0,X5),k1_relat_1(X0))))),
% 4.12/0.99    introduced(choice_axiom,[])).
% 4.12/0.99  
% 4.12/0.99  fof(f42,plain,(
% 4.12/0.99    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK1(X0,X1)) = X2 & r2_hidden(sK1(X0,X1),k1_relat_1(X0))))) )),
% 4.12/0.99    introduced(choice_axiom,[])).
% 4.12/0.99  
% 4.12/0.99  fof(f41,plain,(
% 4.12/0.99    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK0(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK0(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK0(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK0(X0,X1),X1))))),
% 4.12/0.99    introduced(choice_axiom,[])).
% 4.12/0.99  
% 4.12/0.99  fof(f44,plain,(
% 4.12/0.99    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK0(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK0(X0,X1),X1)) & ((k1_funct_1(X0,sK1(X0,X1)) = sK0(X0,X1) & r2_hidden(sK1(X0,X1),k1_relat_1(X0))) | r2_hidden(sK0(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK2(X0,X5)) = X5 & r2_hidden(sK2(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.12/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f40,f43,f42,f41])).
% 4.12/0.99  
% 4.12/0.99  fof(f63,plain,(
% 4.12/0.99    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) | r2_hidden(sK0(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.12/0.99    inference(cnf_transformation,[],[f44])).
% 4.12/0.99  
% 4.12/0.99  fof(f19,conjecture,(
% 4.12/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 4.12/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.12/0.99  
% 4.12/0.99  fof(f20,negated_conjecture,(
% 4.12/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 4.12/0.99    inference(negated_conjecture,[],[f19])).
% 4.12/0.99  
% 4.12/0.99  fof(f36,plain,(
% 4.12/0.99    ? [X0,X1,X2] : ((k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 4.12/0.99    inference(ennf_transformation,[],[f20])).
% 4.12/0.99  
% 4.12/0.99  fof(f37,plain,(
% 4.12/0.99    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 4.12/0.99    inference(flattening,[],[f36])).
% 4.12/0.99  
% 4.12/0.99  fof(f45,plain,(
% 4.12/0.99    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_tarski(k1_funct_1(sK5,sK3)) != k2_relset_1(k1_tarski(sK3),sK4,sK5) & k1_xboole_0 != sK4 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4))) & v1_funct_2(sK5,k1_tarski(sK3),sK4) & v1_funct_1(sK5))),
% 4.12/0.99    introduced(choice_axiom,[])).
% 4.12/0.99  
% 4.12/0.99  fof(f46,plain,(
% 4.12/0.99    k1_tarski(k1_funct_1(sK5,sK3)) != k2_relset_1(k1_tarski(sK3),sK4,sK5) & k1_xboole_0 != sK4 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4))) & v1_funct_2(sK5,k1_tarski(sK3),sK4) & v1_funct_1(sK5)),
% 4.12/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f37,f45])).
% 4.12/0.99  
% 4.12/0.99  fof(f73,plain,(
% 4.12/0.99    v1_funct_1(sK5)),
% 4.12/0.99    inference(cnf_transformation,[],[f46])).
% 4.12/0.99  
% 4.12/0.99  fof(f75,plain,(
% 4.12/0.99    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4)))),
% 4.12/0.99    inference(cnf_transformation,[],[f46])).
% 4.12/0.99  
% 4.12/0.99  fof(f3,axiom,(
% 4.12/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 4.12/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.12/0.99  
% 4.12/0.99  fof(f49,plain,(
% 4.12/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 4.12/0.99    inference(cnf_transformation,[],[f3])).
% 4.12/0.99  
% 4.12/0.99  fof(f4,axiom,(
% 4.12/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 4.12/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.12/0.99  
% 4.12/0.99  fof(f50,plain,(
% 4.12/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 4.12/0.99    inference(cnf_transformation,[],[f4])).
% 4.12/0.99  
% 4.12/0.99  fof(f5,axiom,(
% 4.12/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 4.12/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.12/0.99  
% 4.12/0.99  fof(f51,plain,(
% 4.12/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 4.12/0.99    inference(cnf_transformation,[],[f5])).
% 4.12/0.99  
% 4.12/0.99  fof(f78,plain,(
% 4.12/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 4.12/0.99    inference(definition_unfolding,[],[f50,f51])).
% 4.12/0.99  
% 4.12/0.99  fof(f79,plain,(
% 4.12/0.99    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 4.12/0.99    inference(definition_unfolding,[],[f49,f78])).
% 4.12/0.99  
% 4.12/0.99  fof(f84,plain,(
% 4.12/0.99    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))),
% 4.12/0.99    inference(definition_unfolding,[],[f75,f79])).
% 4.12/0.99  
% 4.12/0.99  fof(f14,axiom,(
% 4.12/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 4.12/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.12/0.99  
% 4.12/0.99  fof(f30,plain,(
% 4.12/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.12/0.99    inference(ennf_transformation,[],[f14])).
% 4.12/0.99  
% 4.12/0.99  fof(f67,plain,(
% 4.12/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.12/0.99    inference(cnf_transformation,[],[f30])).
% 4.12/0.99  
% 4.12/0.99  fof(f11,axiom,(
% 4.12/0.99    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 4.12/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.12/0.99  
% 4.12/0.99  fof(f58,plain,(
% 4.12/0.99    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 4.12/0.99    inference(cnf_transformation,[],[f11])).
% 4.12/0.99  
% 4.12/0.99  fof(f10,axiom,(
% 4.12/0.99    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 4.12/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.12/0.99  
% 4.12/0.99  fof(f25,plain,(
% 4.12/0.99    ! [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 4.12/0.99    inference(ennf_transformation,[],[f10])).
% 4.12/0.99  
% 4.12/0.99  fof(f38,plain,(
% 4.12/0.99    ! [X0,X1] : (((r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0)) & (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)))) | ~v1_relat_1(X1))),
% 4.12/0.99    inference(nnf_transformation,[],[f25])).
% 4.12/0.99  
% 4.12/0.99  fof(f57,plain,(
% 4.12/0.99    ( ! [X0,X1] : (r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 4.12/0.99    inference(cnf_transformation,[],[f38])).
% 4.12/0.99  
% 4.12/0.99  fof(f13,axiom,(
% 4.12/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)))),
% 4.12/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.12/0.99  
% 4.12/0.99  fof(f28,plain,(
% 4.12/0.99    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 4.12/0.99    inference(ennf_transformation,[],[f13])).
% 4.12/0.99  
% 4.12/0.99  fof(f29,plain,(
% 4.12/0.99    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 4.12/0.99    inference(flattening,[],[f28])).
% 4.12/0.99  
% 4.12/0.99  fof(f66,plain,(
% 4.12/0.99    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 4.12/0.99    inference(cnf_transformation,[],[f29])).
% 4.12/0.99  
% 4.12/0.99  fof(f82,plain,(
% 4.12/0.99    ( ! [X0,X1] : (k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 4.12/0.99    inference(definition_unfolding,[],[f66,f79])).
% 4.12/0.99  
% 4.12/0.99  fof(f7,axiom,(
% 4.12/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 4.12/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.12/0.99  
% 4.12/0.99  fof(f53,plain,(
% 4.12/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 4.12/0.99    inference(cnf_transformation,[],[f7])).
% 4.12/0.99  
% 4.12/0.99  fof(f9,axiom,(
% 4.12/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 4.12/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.12/0.99  
% 4.12/0.99  fof(f24,plain,(
% 4.12/0.99    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 4.12/0.99    inference(ennf_transformation,[],[f9])).
% 4.12/0.99  
% 4.12/0.99  fof(f55,plain,(
% 4.12/0.99    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 4.12/0.99    inference(cnf_transformation,[],[f24])).
% 4.12/0.99  
% 4.12/0.99  fof(f81,plain,(
% 4.12/0.99    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 4.12/0.99    inference(definition_unfolding,[],[f55,f79])).
% 4.12/0.99  
% 4.12/0.99  fof(f1,axiom,(
% 4.12/0.99    v1_xboole_0(o_0_0_xboole_0)),
% 4.12/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.12/0.99  
% 4.12/0.99  fof(f47,plain,(
% 4.12/0.99    v1_xboole_0(o_0_0_xboole_0)),
% 4.12/0.99    inference(cnf_transformation,[],[f1])).
% 4.12/0.99  
% 4.12/0.99  fof(f2,axiom,(
% 4.12/0.99    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 4.12/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.12/0.99  
% 4.12/0.99  fof(f21,plain,(
% 4.12/0.99    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 4.12/0.99    inference(ennf_transformation,[],[f2])).
% 4.12/0.99  
% 4.12/0.99  fof(f48,plain,(
% 4.12/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 4.12/0.99    inference(cnf_transformation,[],[f21])).
% 4.12/0.99  
% 4.12/0.99  fof(f16,axiom,(
% 4.12/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 4.12/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.12/0.99  
% 4.12/0.99  fof(f32,plain,(
% 4.12/0.99    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.12/0.99    inference(ennf_transformation,[],[f16])).
% 4.12/0.99  
% 4.12/0.99  fof(f69,plain,(
% 4.12/0.99    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.12/0.99    inference(cnf_transformation,[],[f32])).
% 4.12/0.99  
% 4.12/0.99  fof(f17,axiom,(
% 4.12/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 4.12/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.12/0.99  
% 4.12/0.99  fof(f33,plain,(
% 4.12/0.99    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.12/0.99    inference(ennf_transformation,[],[f17])).
% 4.12/0.99  
% 4.12/0.99  fof(f70,plain,(
% 4.12/0.99    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.12/0.99    inference(cnf_transformation,[],[f33])).
% 4.12/0.99  
% 4.12/0.99  fof(f15,axiom,(
% 4.12/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 4.12/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.12/0.99  
% 4.12/0.99  fof(f31,plain,(
% 4.12/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.12/0.99    inference(ennf_transformation,[],[f15])).
% 4.12/0.99  
% 4.12/0.99  fof(f68,plain,(
% 4.12/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.12/0.99    inference(cnf_transformation,[],[f31])).
% 4.12/0.99  
% 4.12/0.99  fof(f56,plain,(
% 4.12/0.99    ( ! [X0,X1] : (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 4.12/0.99    inference(cnf_transformation,[],[f38])).
% 4.12/0.99  
% 4.12/0.99  fof(f59,plain,(
% 4.12/0.99    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 4.12/0.99    inference(cnf_transformation,[],[f11])).
% 4.12/0.99  
% 4.12/0.99  fof(f77,plain,(
% 4.12/0.99    k1_tarski(k1_funct_1(sK5,sK3)) != k2_relset_1(k1_tarski(sK3),sK4,sK5)),
% 4.12/0.99    inference(cnf_transformation,[],[f46])).
% 4.12/0.99  
% 4.12/0.99  fof(f83,plain,(
% 4.12/0.99    k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5)),
% 4.12/0.99    inference(definition_unfolding,[],[f77,f79,f79])).
% 4.12/0.99  
% 4.12/0.99  fof(f62,plain,(
% 4.12/0.99    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.12/0.99    inference(cnf_transformation,[],[f44])).
% 4.12/0.99  
% 4.12/0.99  fof(f86,plain,(
% 4.12/0.99    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.12/0.99    inference(equality_resolution,[],[f62])).
% 4.12/0.99  
% 4.12/0.99  fof(f87,plain,(
% 4.12/0.99    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.12/0.99    inference(equality_resolution,[],[f86])).
% 4.12/0.99  
% 4.12/0.99  fof(f18,axiom,(
% 4.12/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 4.12/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.12/0.99  
% 4.12/0.99  fof(f34,plain,(
% 4.12/0.99    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 4.12/0.99    inference(ennf_transformation,[],[f18])).
% 4.12/0.99  
% 4.12/0.99  fof(f35,plain,(
% 4.12/0.99    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 4.12/0.99    inference(flattening,[],[f34])).
% 4.12/0.99  
% 4.12/0.99  fof(f72,plain,(
% 4.12/0.99    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 4.12/0.99    inference(cnf_transformation,[],[f35])).
% 4.12/0.99  
% 4.12/0.99  fof(f74,plain,(
% 4.12/0.99    v1_funct_2(sK5,k1_tarski(sK3),sK4)),
% 4.12/0.99    inference(cnf_transformation,[],[f46])).
% 4.12/0.99  
% 4.12/0.99  fof(f85,plain,(
% 4.12/0.99    v1_funct_2(sK5,k2_enumset1(sK3,sK3,sK3,sK3),sK4)),
% 4.12/0.99    inference(definition_unfolding,[],[f74,f79])).
% 4.12/0.99  
% 4.12/0.99  fof(f76,plain,(
% 4.12/0.99    k1_xboole_0 != sK4),
% 4.12/0.99    inference(cnf_transformation,[],[f46])).
% 4.12/0.99  
% 4.12/0.99  fof(f6,axiom,(
% 4.12/0.99    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 4.12/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.12/0.99  
% 4.12/0.99  fof(f52,plain,(
% 4.12/0.99    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 4.12/0.99    inference(cnf_transformation,[],[f6])).
% 4.12/0.99  
% 4.12/0.99  fof(f80,plain,(
% 4.12/0.99    ( ! [X0] : (~v1_xboole_0(k2_enumset1(X0,X0,X0,X0))) )),
% 4.12/0.99    inference(definition_unfolding,[],[f52,f79])).
% 4.12/0.99  
% 4.12/0.99  fof(f60,plain,(
% 4.12/0.99    ( ! [X0,X5,X1] : (r2_hidden(sK2(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.12/0.99    inference(cnf_transformation,[],[f44])).
% 4.12/0.99  
% 4.12/0.99  fof(f89,plain,(
% 4.12/0.99    ( ! [X0,X5] : (r2_hidden(sK2(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.12/0.99    inference(equality_resolution,[],[f60])).
% 4.12/0.99  
% 4.12/0.99  cnf(c_12,plain,
% 4.12/0.99      ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
% 4.12/0.99      | r2_hidden(sK0(X0,X1),X1)
% 4.12/0.99      | ~ v1_funct_1(X0)
% 4.12/0.99      | ~ v1_relat_1(X0)
% 4.12/0.99      | k2_relat_1(X0) = X1 ),
% 4.12/0.99      inference(cnf_transformation,[],[f63]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_27,negated_conjecture,
% 4.12/0.99      ( v1_funct_1(sK5) ),
% 4.12/0.99      inference(cnf_transformation,[],[f73]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_316,plain,
% 4.12/0.99      ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
% 4.12/0.99      | r2_hidden(sK0(X0,X1),X1)
% 4.12/0.99      | ~ v1_relat_1(X0)
% 4.12/0.99      | k2_relat_1(X0) = X1
% 4.12/0.99      | sK5 != X0 ),
% 4.12/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_27]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_317,plain,
% 4.12/0.99      ( r2_hidden(sK1(sK5,X0),k1_relat_1(sK5))
% 4.12/0.99      | r2_hidden(sK0(sK5,X0),X0)
% 4.12/0.99      | ~ v1_relat_1(sK5)
% 4.12/0.99      | k2_relat_1(sK5) = X0 ),
% 4.12/0.99      inference(unflattening,[status(thm)],[c_316]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_1348,plain,
% 4.12/0.99      ( k2_relat_1(sK5) = X0
% 4.12/0.99      | r2_hidden(sK1(sK5,X0),k1_relat_1(sK5)) = iProver_top
% 4.12/0.99      | r2_hidden(sK0(sK5,X0),X0) = iProver_top
% 4.12/0.99      | v1_relat_1(sK5) != iProver_top ),
% 4.12/0.99      inference(predicate_to_equality,[status(thm)],[c_317]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_25,negated_conjecture,
% 4.12/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) ),
% 4.12/0.99      inference(cnf_transformation,[],[f84]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_30,plain,
% 4.12/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) = iProver_top ),
% 4.12/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_318,plain,
% 4.12/0.99      ( k2_relat_1(sK5) = X0
% 4.12/0.99      | r2_hidden(sK1(sK5,X0),k1_relat_1(sK5)) = iProver_top
% 4.12/0.99      | r2_hidden(sK0(sK5,X0),X0) = iProver_top
% 4.12/0.99      | v1_relat_1(sK5) != iProver_top ),
% 4.12/0.99      inference(predicate_to_equality,[status(thm)],[c_317]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_17,plain,
% 4.12/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 4.12/0.99      inference(cnf_transformation,[],[f67]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_1445,plain,
% 4.12/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))
% 4.12/0.99      | v1_relat_1(sK5) ),
% 4.12/0.99      inference(instantiation,[status(thm)],[c_17]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_1446,plain,
% 4.12/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) != iProver_top
% 4.12/0.99      | v1_relat_1(sK5) = iProver_top ),
% 4.12/0.99      inference(predicate_to_equality,[status(thm)],[c_1445]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_3262,plain,
% 4.12/0.99      ( r2_hidden(sK0(sK5,X0),X0) = iProver_top
% 4.12/0.99      | r2_hidden(sK1(sK5,X0),k1_relat_1(sK5)) = iProver_top
% 4.12/0.99      | k2_relat_1(sK5) = X0 ),
% 4.12/0.99      inference(global_propositional_subsumption,
% 4.12/0.99                [status(thm)],
% 4.12/0.99                [c_1348,c_30,c_318,c_1446]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_3263,plain,
% 4.12/0.99      ( k2_relat_1(sK5) = X0
% 4.12/0.99      | r2_hidden(sK1(sK5,X0),k1_relat_1(sK5)) = iProver_top
% 4.12/0.99      | r2_hidden(sK0(sK5,X0),X0) = iProver_top ),
% 4.12/0.99      inference(renaming,[status(thm)],[c_3262]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_9,plain,
% 4.12/0.99      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 4.12/0.99      inference(cnf_transformation,[],[f58]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_6,plain,
% 4.12/0.99      ( r2_hidden(X0,k1_relat_1(X1))
% 4.12/0.99      | ~ v1_relat_1(X1)
% 4.12/0.99      | k11_relat_1(X1,X0) = k1_xboole_0 ),
% 4.12/0.99      inference(cnf_transformation,[],[f57]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_1357,plain,
% 4.12/0.99      ( k11_relat_1(X0,X1) = k1_xboole_0
% 4.12/0.99      | r2_hidden(X1,k1_relat_1(X0)) = iProver_top
% 4.12/0.99      | v1_relat_1(X0) != iProver_top ),
% 4.12/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_16,plain,
% 4.12/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 4.12/0.99      | ~ v1_funct_1(X1)
% 4.12/0.99      | ~ v1_relat_1(X1)
% 4.12/0.99      | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ),
% 4.12/0.99      inference(cnf_transformation,[],[f82]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_352,plain,
% 4.12/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 4.12/0.99      | ~ v1_relat_1(X1)
% 4.12/0.99      | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
% 4.12/0.99      | sK5 != X1 ),
% 4.12/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_27]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_353,plain,
% 4.12/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK5))
% 4.12/0.99      | ~ v1_relat_1(sK5)
% 4.12/0.99      | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k11_relat_1(sK5,X0) ),
% 4.12/0.99      inference(unflattening,[status(thm)],[c_352]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_1346,plain,
% 4.12/0.99      ( k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k11_relat_1(sK5,X0)
% 4.12/0.99      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 4.12/0.99      | v1_relat_1(sK5) != iProver_top ),
% 4.12/0.99      inference(predicate_to_equality,[status(thm)],[c_353]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_1794,plain,
% 4.12/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK5))
% 4.12/0.99      | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k11_relat_1(sK5,X0) ),
% 4.12/0.99      inference(global_propositional_subsumption,
% 4.12/0.99                [status(thm)],
% 4.12/0.99                [c_353,c_25,c_1445]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_1796,plain,
% 4.12/0.99      ( k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k11_relat_1(sK5,X0)
% 4.12/0.99      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 4.12/0.99      inference(predicate_to_equality,[status(thm)],[c_1794]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_2666,plain,
% 4.12/0.99      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 4.12/0.99      | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k11_relat_1(sK5,X0) ),
% 4.12/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1346,c_1796]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_2667,plain,
% 4.12/0.99      ( k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k11_relat_1(sK5,X0)
% 4.12/0.99      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 4.12/0.99      inference(renaming,[status(thm)],[c_2666]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_2670,plain,
% 4.12/0.99      ( k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k11_relat_1(sK5,X0)
% 4.12/0.99      | k11_relat_1(sK5,X0) = k1_xboole_0
% 4.12/0.99      | v1_relat_1(sK5) != iProver_top ),
% 4.12/0.99      inference(superposition,[status(thm)],[c_1357,c_2667]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_2672,plain,
% 4.12/0.99      ( ~ v1_relat_1(sK5)
% 4.12/0.99      | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k11_relat_1(sK5,X0)
% 4.12/0.99      | k11_relat_1(sK5,X0) = k1_xboole_0 ),
% 4.12/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2670]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_3890,plain,
% 4.12/0.99      ( k11_relat_1(sK5,X0) = k1_xboole_0
% 4.12/0.99      | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k11_relat_1(sK5,X0) ),
% 4.12/0.99      inference(global_propositional_subsumption,
% 4.12/0.99                [status(thm)],
% 4.12/0.99                [c_2670,c_25,c_1445,c_2672]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_3891,plain,
% 4.12/0.99      ( k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k11_relat_1(sK5,X0)
% 4.12/0.99      | k11_relat_1(sK5,X0) = k1_xboole_0 ),
% 4.12/0.99      inference(renaming,[status(thm)],[c_3890]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_3,plain,
% 4.12/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 4.12/0.99      inference(cnf_transformation,[],[f53]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_1360,plain,
% 4.12/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 4.12/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_1355,plain,
% 4.12/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 4.12/0.99      | v1_relat_1(X0) = iProver_top ),
% 4.12/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_1684,plain,
% 4.12/0.99      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 4.12/0.99      inference(superposition,[status(thm)],[c_1360,c_1355]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_5,plain,
% 4.12/0.99      ( ~ v1_relat_1(X0)
% 4.12/0.99      | k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
% 4.12/0.99      inference(cnf_transformation,[],[f81]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_1358,plain,
% 4.12/0.99      ( k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1)
% 4.12/0.99      | v1_relat_1(X0) != iProver_top ),
% 4.12/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_2274,plain,
% 4.12/0.99      ( k9_relat_1(k1_xboole_0,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(k1_xboole_0,X0) ),
% 4.12/0.99      inference(superposition,[status(thm)],[c_1684,c_1358]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_3894,plain,
% 4.12/0.99      ( k9_relat_1(k1_xboole_0,k11_relat_1(sK5,X0)) = k11_relat_1(k1_xboole_0,k1_funct_1(sK5,X0))
% 4.12/0.99      | k11_relat_1(sK5,X0) = k1_xboole_0 ),
% 4.12/0.99      inference(superposition,[status(thm)],[c_3891,c_2274]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_0,plain,
% 4.12/0.99      ( v1_xboole_0(o_0_0_xboole_0) ),
% 4.12/0.99      inference(cnf_transformation,[],[f47]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_1,plain,
% 4.12/0.99      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 4.12/0.99      inference(cnf_transformation,[],[f48]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_283,plain,
% 4.12/0.99      ( k1_xboole_0 = X0 | o_0_0_xboole_0 != X0 ),
% 4.12/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_1]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_284,plain,
% 4.12/0.99      ( k1_xboole_0 = o_0_0_xboole_0 ),
% 4.12/0.99      inference(unflattening,[status(thm)],[c_283]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_19,plain,
% 4.12/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.12/0.99      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 4.12/0.99      inference(cnf_transformation,[],[f69]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_1353,plain,
% 4.12/0.99      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 4.12/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 4.12/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_2043,plain,
% 4.12/0.99      ( k7_relset_1(X0,X1,k1_xboole_0,X2) = k9_relat_1(k1_xboole_0,X2) ),
% 4.12/0.99      inference(superposition,[status(thm)],[c_1360,c_1353]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_2588,plain,
% 4.12/0.99      ( k7_relset_1(X0,X1,o_0_0_xboole_0,X2) = k9_relat_1(k1_xboole_0,X2) ),
% 4.12/0.99      inference(superposition,[status(thm)],[c_284,c_2043]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_1601,plain,
% 4.12/0.99      ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 4.12/0.99      inference(superposition,[status(thm)],[c_284,c_1360]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_21,plain,
% 4.12/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.12/0.99      | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
% 4.12/0.99      inference(cnf_transformation,[],[f70]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_1351,plain,
% 4.12/0.99      ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
% 4.12/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 4.12/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_2513,plain,
% 4.12/0.99      ( k7_relset_1(X0,X1,o_0_0_xboole_0,X0) = k2_relset_1(X0,X1,o_0_0_xboole_0) ),
% 4.12/0.99      inference(superposition,[status(thm)],[c_1601,c_1351]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_4964,plain,
% 4.12/0.99      ( k2_relset_1(X0,X1,o_0_0_xboole_0) = k9_relat_1(k1_xboole_0,X0) ),
% 4.12/0.99      inference(superposition,[status(thm)],[c_2588,c_2513]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_18,plain,
% 4.12/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.12/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 4.12/0.99      inference(cnf_transformation,[],[f68]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_1354,plain,
% 4.12/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 4.12/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 4.12/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_2515,plain,
% 4.12/0.99      ( k2_relset_1(X0,X1,o_0_0_xboole_0) = k2_relat_1(o_0_0_xboole_0) ),
% 4.12/0.99      inference(superposition,[status(thm)],[c_1601,c_1354]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_6929,plain,
% 4.12/0.99      ( k9_relat_1(k1_xboole_0,X0) = k2_relat_1(o_0_0_xboole_0) ),
% 4.12/0.99      inference(superposition,[status(thm)],[c_4964,c_2515]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_8324,plain,
% 4.12/0.99      ( k11_relat_1(sK5,X0) = k1_xboole_0
% 4.12/0.99      | k11_relat_1(k1_xboole_0,k1_funct_1(sK5,X0)) = k2_relat_1(o_0_0_xboole_0) ),
% 4.12/0.99      inference(superposition,[status(thm)],[c_3894,c_6929]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_7,plain,
% 4.12/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 4.12/0.99      | ~ v1_relat_1(X1)
% 4.12/0.99      | k11_relat_1(X1,X0) != k1_xboole_0 ),
% 4.12/0.99      inference(cnf_transformation,[],[f56]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_1356,plain,
% 4.12/0.99      ( k11_relat_1(X0,X1) != k1_xboole_0
% 4.12/0.99      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 4.12/0.99      | v1_relat_1(X0) != iProver_top ),
% 4.12/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_9585,plain,
% 4.12/0.99      ( k11_relat_1(sK5,X0) = k1_xboole_0
% 4.12/0.99      | k2_relat_1(o_0_0_xboole_0) != k1_xboole_0
% 4.12/0.99      | r2_hidden(k1_funct_1(sK5,X0),k1_relat_1(k1_xboole_0)) != iProver_top
% 4.12/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 4.12/0.99      inference(superposition,[status(thm)],[c_8324,c_1356]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_8,plain,
% 4.12/0.99      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 4.12/0.99      inference(cnf_transformation,[],[f59]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_1410,plain,
% 4.12/0.99      ( k2_relat_1(o_0_0_xboole_0) = k1_xboole_0 ),
% 4.12/0.99      inference(superposition,[status(thm)],[c_284,c_8]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_1435,plain,
% 4.12/0.99      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.12/0.99      | v1_relat_1(k1_xboole_0) ),
% 4.12/0.99      inference(instantiation,[status(thm)],[c_17]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_1437,plain,
% 4.12/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.12/0.99      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 4.12/0.99      inference(predicate_to_equality,[status(thm)],[c_1435]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_1436,plain,
% 4.12/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 4.12/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_1441,plain,
% 4.12/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
% 4.12/0.99      inference(predicate_to_equality,[status(thm)],[c_1436]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_10087,plain,
% 4.12/0.99      ( r2_hidden(k1_funct_1(sK5,X0),k1_relat_1(k1_xboole_0)) != iProver_top
% 4.12/0.99      | k11_relat_1(sK5,X0) = k1_xboole_0 ),
% 4.12/0.99      inference(global_propositional_subsumption,
% 4.12/0.99                [status(thm)],
% 4.12/0.99                [c_9585,c_1410,c_1437,c_1441]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_10088,plain,
% 4.12/0.99      ( k11_relat_1(sK5,X0) = k1_xboole_0
% 4.12/0.99      | r2_hidden(k1_funct_1(sK5,X0),k1_relat_1(k1_xboole_0)) != iProver_top ),
% 4.12/0.99      inference(renaming,[status(thm)],[c_10087]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_10097,plain,
% 4.12/0.99      ( k11_relat_1(sK5,X0) = k1_xboole_0
% 4.12/0.99      | r2_hidden(k1_funct_1(sK5,X0),k1_xboole_0) != iProver_top ),
% 4.12/0.99      inference(superposition,[status(thm)],[c_9,c_10088]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_1584,plain,
% 4.12/0.99      ( r2_hidden(X0,k1_relat_1(sK5))
% 4.12/0.99      | ~ v1_relat_1(sK5)
% 4.12/0.99      | k11_relat_1(sK5,X0) = k1_xboole_0 ),
% 4.12/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_1585,plain,
% 4.12/0.99      ( k11_relat_1(sK5,X0) = k1_xboole_0
% 4.12/0.99      | r2_hidden(X0,k1_relat_1(sK5)) = iProver_top
% 4.12/0.99      | v1_relat_1(sK5) != iProver_top ),
% 4.12/0.99      inference(predicate_to_equality,[status(thm)],[c_1584]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_1350,plain,
% 4.12/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) = iProver_top ),
% 4.12/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_1685,plain,
% 4.12/0.99      ( v1_relat_1(sK5) = iProver_top ),
% 4.12/0.99      inference(superposition,[status(thm)],[c_1350,c_1355]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_2408,plain,
% 4.12/0.99      ( k9_relat_1(sK5,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK5,X0) ),
% 4.12/0.99      inference(superposition,[status(thm)],[c_1685,c_1358]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_2044,plain,
% 4.12/0.99      ( k7_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5,X0) = k9_relat_1(sK5,X0) ),
% 4.12/0.99      inference(superposition,[status(thm)],[c_1350,c_1353]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_2105,plain,
% 4.12/0.99      ( k7_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5,k2_enumset1(sK3,sK3,sK3,sK3)) = k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) ),
% 4.12/0.99      inference(superposition,[status(thm)],[c_1350,c_1351]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_3887,plain,
% 4.12/0.99      ( k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k9_relat_1(sK5,k2_enumset1(sK3,sK3,sK3,sK3)) ),
% 4.12/0.99      inference(superposition,[status(thm)],[c_2044,c_2105]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_1767,plain,
% 4.12/0.99      ( k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_relat_1(sK5) ),
% 4.12/0.99      inference(superposition,[status(thm)],[c_1350,c_1354]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_8024,plain,
% 4.12/0.99      ( k9_relat_1(sK5,k2_enumset1(sK3,sK3,sK3,sK3)) = k2_relat_1(sK5) ),
% 4.12/0.99      inference(superposition,[status(thm)],[c_3887,c_1767]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_8109,plain,
% 4.12/0.99      ( k11_relat_1(sK5,sK3) = k2_relat_1(sK5) ),
% 4.12/0.99      inference(superposition,[status(thm)],[c_2408,c_8024]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_23,negated_conjecture,
% 4.12/0.99      ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) ),
% 4.12/0.99      inference(cnf_transformation,[],[f83]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_3896,plain,
% 4.12/0.99      ( k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) != k11_relat_1(sK5,sK3)
% 4.12/0.99      | k11_relat_1(sK5,sK3) = k1_xboole_0 ),
% 4.12/0.99      inference(superposition,[status(thm)],[c_3891,c_23]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_8022,plain,
% 4.12/0.99      ( k9_relat_1(sK5,k2_enumset1(sK3,sK3,sK3,sK3)) != k11_relat_1(sK5,sK3)
% 4.12/0.99      | k11_relat_1(sK5,sK3) = k1_xboole_0 ),
% 4.12/0.99      inference(superposition,[status(thm)],[c_3887,c_3896]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_1573,plain,
% 4.12/0.99      ( ~ v1_relat_1(sK5)
% 4.12/0.99      | k9_relat_1(sK5,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK5,X0) ),
% 4.12/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_1580,plain,
% 4.12/0.99      ( ~ v1_relat_1(sK5)
% 4.12/0.99      | k9_relat_1(sK5,k2_enumset1(sK3,sK3,sK3,sK3)) = k11_relat_1(sK5,sK3) ),
% 4.12/0.99      inference(instantiation,[status(thm)],[c_1573]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_968,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_1595,plain,
% 4.12/0.99      ( X0 != X1
% 4.12/0.99      | k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != X1
% 4.12/0.99      | k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) = X0 ),
% 4.12/0.99      inference(instantiation,[status(thm)],[c_968]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_2144,plain,
% 4.12/0.99      ( X0 != k11_relat_1(sK5,sK3)
% 4.12/0.99      | k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) = X0
% 4.12/0.99      | k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k11_relat_1(sK5,sK3) ),
% 4.12/0.99      inference(instantiation,[status(thm)],[c_1595]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_2661,plain,
% 4.12/0.99      ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) = k9_relat_1(sK5,k2_enumset1(sK3,sK3,sK3,sK3))
% 4.12/0.99      | k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k11_relat_1(sK5,sK3)
% 4.12/0.99      | k9_relat_1(sK5,k2_enumset1(sK3,sK3,sK3,sK3)) != k11_relat_1(sK5,sK3) ),
% 4.12/0.99      inference(instantiation,[status(thm)],[c_2144]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_2673,plain,
% 4.12/0.99      ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) = k11_relat_1(sK5,sK3)
% 4.12/0.99      | k11_relat_1(sK5,sK3) = k1_xboole_0
% 4.12/0.99      | v1_relat_1(sK5) != iProver_top ),
% 4.12/0.99      inference(instantiation,[status(thm)],[c_2670]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_1485,plain,
% 4.12/0.99      ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != X0
% 4.12/0.99      | k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) = k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5)
% 4.12/0.99      | k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) != X0 ),
% 4.12/0.99      inference(instantiation,[status(thm)],[c_968]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_4957,plain,
% 4.12/0.99      ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) = k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5)
% 4.12/0.99      | k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k9_relat_1(sK5,k2_enumset1(sK3,sK3,sK3,sK3))
% 4.12/0.99      | k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) != k9_relat_1(sK5,k2_enumset1(sK3,sK3,sK3,sK3)) ),
% 4.12/0.99      inference(instantiation,[status(thm)],[c_1485]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_8028,plain,
% 4.12/0.99      ( k11_relat_1(sK5,sK3) = k1_xboole_0 ),
% 4.12/0.99      inference(global_propositional_subsumption,
% 4.12/0.99                [status(thm)],
% 4.12/0.99                [c_8022,c_25,c_30,c_23,c_1445,c_1446,c_1580,c_2661,c_2673,
% 4.12/0.99                 c_3887,c_4957]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_8154,plain,
% 4.12/0.99      ( k2_relat_1(sK5) = k1_xboole_0 ),
% 4.12/0.99      inference(superposition,[status(thm)],[c_8109,c_8028]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_13,plain,
% 4.12/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 4.12/0.99      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 4.12/0.99      | ~ v1_funct_1(X1)
% 4.12/0.99      | ~ v1_relat_1(X1) ),
% 4.12/0.99      inference(cnf_transformation,[],[f87]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_397,plain,
% 4.12/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 4.12/0.99      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 4.12/0.99      | ~ v1_relat_1(X1)
% 4.12/0.99      | sK5 != X1 ),
% 4.12/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_27]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_398,plain,
% 4.12/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK5))
% 4.12/0.99      | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5))
% 4.12/0.99      | ~ v1_relat_1(sK5) ),
% 4.12/0.99      inference(unflattening,[status(thm)],[c_397]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_1343,plain,
% 4.12/0.99      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 4.12/0.99      | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) = iProver_top
% 4.12/0.99      | v1_relat_1(sK5) != iProver_top ),
% 4.12/0.99      inference(predicate_to_equality,[status(thm)],[c_398]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_1498,plain,
% 4.12/0.99      ( r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5))
% 4.12/0.99      | ~ r2_hidden(X0,k1_relat_1(sK5)) ),
% 4.12/0.99      inference(global_propositional_subsumption,
% 4.12/0.99                [status(thm)],
% 4.12/0.99                [c_398,c_25,c_1445]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_1499,plain,
% 4.12/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK5))
% 4.12/0.99      | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) ),
% 4.12/0.99      inference(renaming,[status(thm)],[c_1498]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_1500,plain,
% 4.12/0.99      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 4.12/0.99      | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) = iProver_top ),
% 4.12/0.99      inference(predicate_to_equality,[status(thm)],[c_1499]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_1930,plain,
% 4.12/0.99      ( r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) = iProver_top
% 4.12/0.99      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 4.12/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1343,c_1500]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_1931,plain,
% 4.12/0.99      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 4.12/0.99      | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) = iProver_top ),
% 4.12/0.99      inference(renaming,[status(thm)],[c_1930]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_9477,plain,
% 4.12/0.99      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 4.12/0.99      | r2_hidden(k1_funct_1(sK5,X0),k1_xboole_0) = iProver_top ),
% 4.12/0.99      inference(superposition,[status(thm)],[c_8154,c_1931]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_10106,plain,
% 4.12/0.99      ( k11_relat_1(sK5,X0) = k1_xboole_0 ),
% 4.12/0.99      inference(global_propositional_subsumption,
% 4.12/0.99                [status(thm)],
% 4.12/0.99                [c_10097,c_30,c_1446,c_1585,c_9477]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_10109,plain,
% 4.12/0.99      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 4.12/0.99      | v1_relat_1(sK5) != iProver_top ),
% 4.12/0.99      inference(superposition,[status(thm)],[c_10106,c_1356]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_1583,plain,
% 4.12/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK5))
% 4.12/0.99      | ~ v1_relat_1(sK5)
% 4.12/0.99      | k11_relat_1(sK5,X0) != k1_xboole_0 ),
% 4.12/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_1589,plain,
% 4.12/0.99      ( k11_relat_1(sK5,X0) != k1_xboole_0
% 4.12/0.99      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 4.12/0.99      | v1_relat_1(sK5) != iProver_top ),
% 4.12/0.99      inference(predicate_to_equality,[status(thm)],[c_1583]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_10209,plain,
% 4.12/0.99      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 4.12/0.99      inference(global_propositional_subsumption,
% 4.12/0.99                [status(thm)],
% 4.12/0.99                [c_10109,c_30,c_1446,c_1585,c_1589,c_9477,c_10097]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_10214,plain,
% 4.12/0.99      ( k2_relat_1(sK5) = X0 | r2_hidden(sK0(sK5,X0),X0) = iProver_top ),
% 4.12/0.99      inference(superposition,[status(thm)],[c_3263,c_10209]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_22,plain,
% 4.12/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 4.12/0.99      | ~ r2_hidden(X3,X1)
% 4.12/0.99      | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
% 4.12/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.12/0.99      | ~ v1_funct_1(X0)
% 4.12/0.99      | k1_xboole_0 = X2 ),
% 4.12/0.99      inference(cnf_transformation,[],[f72]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_26,negated_conjecture,
% 4.12/0.99      ( v1_funct_2(sK5,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
% 4.12/0.99      inference(cnf_transformation,[],[f85]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_295,plain,
% 4.12/0.99      ( ~ r2_hidden(X0,X1)
% 4.12/0.99      | r2_hidden(k1_funct_1(X2,X0),k2_relset_1(X1,X3,X2))
% 4.12/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 4.12/0.99      | ~ v1_funct_1(X2)
% 4.12/0.99      | k2_enumset1(sK3,sK3,sK3,sK3) != X1
% 4.12/0.99      | sK4 != X3
% 4.12/0.99      | sK5 != X2
% 4.12/0.99      | k1_xboole_0 = X3 ),
% 4.12/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_26]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_296,plain,
% 4.12/0.99      ( ~ r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3))
% 4.12/0.99      | r2_hidden(k1_funct_1(sK5,X0),k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5))
% 4.12/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))
% 4.12/0.99      | ~ v1_funct_1(sK5)
% 4.12/0.99      | k1_xboole_0 = sK4 ),
% 4.12/0.99      inference(unflattening,[status(thm)],[c_295]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_24,negated_conjecture,
% 4.12/0.99      ( k1_xboole_0 != sK4 ),
% 4.12/0.99      inference(cnf_transformation,[],[f76]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_300,plain,
% 4.12/0.99      ( r2_hidden(k1_funct_1(sK5,X0),k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5))
% 4.12/0.99      | ~ r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) ),
% 4.12/0.99      inference(global_propositional_subsumption,
% 4.12/0.99                [status(thm)],
% 4.12/0.99                [c_296,c_27,c_25,c_24]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_301,plain,
% 4.12/0.99      ( ~ r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3))
% 4.12/0.99      | r2_hidden(k1_funct_1(sK5,X0),k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5)) ),
% 4.12/0.99      inference(renaming,[status(thm)],[c_300]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_1349,plain,
% 4.12/0.99      ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top
% 4.12/0.99      | r2_hidden(k1_funct_1(sK5,X0),k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5)) = iProver_top ),
% 4.12/0.99      inference(predicate_to_equality,[status(thm)],[c_301]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_3548,plain,
% 4.12/0.99      ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top
% 4.12/0.99      | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) = iProver_top ),
% 4.12/0.99      inference(superposition,[status(thm)],[c_1767,c_1349]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_10756,plain,
% 4.12/0.99      ( k2_enumset1(sK3,sK3,sK3,sK3) = k2_relat_1(sK5)
% 4.12/0.99      | r2_hidden(k1_funct_1(sK5,sK0(sK5,k2_enumset1(sK3,sK3,sK3,sK3))),k2_relat_1(sK5)) = iProver_top ),
% 4.12/0.99      inference(superposition,[status(thm)],[c_10214,c_3548]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_2,plain,
% 4.12/0.99      ( ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
% 4.12/0.99      inference(cnf_transformation,[],[f80]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_288,plain,
% 4.12/0.99      ( k2_enumset1(X0,X0,X0,X0) != o_0_0_xboole_0 ),
% 4.12/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_2]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_289,plain,
% 4.12/0.99      ( k2_enumset1(sK3,sK3,sK3,sK3) != o_0_0_xboole_0 ),
% 4.12/0.99      inference(instantiation,[status(thm)],[c_288]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_967,plain,( X0 = X0 ),theory(equality) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_2069,plain,
% 4.12/0.99      ( o_0_0_xboole_0 = o_0_0_xboole_0 ),
% 4.12/0.99      inference(instantiation,[status(thm)],[c_967]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_1724,plain,
% 4.12/0.99      ( X0 != X1 | o_0_0_xboole_0 != X1 | o_0_0_xboole_0 = X0 ),
% 4.12/0.99      inference(instantiation,[status(thm)],[c_968]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_2068,plain,
% 4.12/0.99      ( X0 != o_0_0_xboole_0
% 4.12/0.99      | o_0_0_xboole_0 = X0
% 4.12/0.99      | o_0_0_xboole_0 != o_0_0_xboole_0 ),
% 4.12/0.99      inference(instantiation,[status(thm)],[c_1724]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_3518,plain,
% 4.12/0.99      ( k2_relat_1(sK5) != o_0_0_xboole_0
% 4.12/0.99      | o_0_0_xboole_0 = k2_relat_1(sK5)
% 4.12/0.99      | o_0_0_xboole_0 != o_0_0_xboole_0 ),
% 4.12/0.99      inference(instantiation,[status(thm)],[c_2068]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_3268,plain,
% 4.12/0.99      ( k2_enumset1(k1_funct_1(sK5,sK1(sK5,X0)),k1_funct_1(sK5,sK1(sK5,X0)),k1_funct_1(sK5,sK1(sK5,X0)),k1_funct_1(sK5,sK1(sK5,X0))) = k11_relat_1(sK5,sK1(sK5,X0))
% 4.12/0.99      | k2_relat_1(sK5) = X0
% 4.12/0.99      | r2_hidden(sK0(sK5,X0),X0) = iProver_top ),
% 4.12/0.99      inference(superposition,[status(thm)],[c_3263,c_2667]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_2104,plain,
% 4.12/0.99      ( k7_relset_1(X0,X1,k1_xboole_0,X0) = k2_relset_1(X0,X1,k1_xboole_0) ),
% 4.12/0.99      inference(superposition,[status(thm)],[c_1360,c_1351]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_2756,plain,
% 4.12/0.99      ( k2_relset_1(X0,X1,k1_xboole_0) = k9_relat_1(k1_xboole_0,X0) ),
% 4.12/0.99      inference(superposition,[status(thm)],[c_2104,c_2043]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_1766,plain,
% 4.12/0.99      ( k2_relset_1(X0,X1,k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
% 4.12/0.99      inference(superposition,[status(thm)],[c_1360,c_1354]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_5124,plain,
% 4.12/0.99      ( k9_relat_1(k1_xboole_0,X0) = k2_relat_1(k1_xboole_0) ),
% 4.12/0.99      inference(superposition,[status(thm)],[c_2756,c_1766]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_5129,plain,
% 4.12/0.99      ( k11_relat_1(k1_xboole_0,X0) = k2_relat_1(k1_xboole_0) ),
% 4.12/0.99      inference(superposition,[status(thm)],[c_5124,c_2274]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_5364,plain,
% 4.12/0.99      ( k2_relat_1(k1_xboole_0) != k1_xboole_0
% 4.12/0.99      | r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top
% 4.12/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 4.12/0.99      inference(superposition,[status(thm)],[c_5129,c_1356]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_5680,plain,
% 4.12/0.99      ( r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top ),
% 4.12/0.99      inference(global_propositional_subsumption,
% 4.12/0.99                [status(thm)],
% 4.12/0.99                [c_5364,c_8,c_1437,c_1441]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_5689,plain,
% 4.12/0.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 4.12/0.99      inference(superposition,[status(thm)],[c_9,c_5680]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_5706,plain,
% 4.12/0.99      ( r2_hidden(X0,o_0_0_xboole_0) != iProver_top ),
% 4.12/0.99      inference(superposition,[status(thm)],[c_284,c_5689]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_7468,plain,
% 4.12/0.99      ( k2_enumset1(k1_funct_1(sK5,sK1(sK5,o_0_0_xboole_0)),k1_funct_1(sK5,sK1(sK5,o_0_0_xboole_0)),k1_funct_1(sK5,sK1(sK5,o_0_0_xboole_0)),k1_funct_1(sK5,sK1(sK5,o_0_0_xboole_0))) = k11_relat_1(sK5,sK1(sK5,o_0_0_xboole_0))
% 4.12/0.99      | k2_relat_1(sK5) = o_0_0_xboole_0 ),
% 4.12/0.99      inference(superposition,[status(thm)],[c_3268,c_5706]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_8767,plain,
% 4.12/0.99      ( k11_relat_1(sK5,sK1(sK5,o_0_0_xboole_0)) != o_0_0_xboole_0
% 4.12/0.99      | k2_relat_1(sK5) = o_0_0_xboole_0 ),
% 4.12/0.99      inference(superposition,[status(thm)],[c_7468,c_288]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_10122,plain,
% 4.12/0.99      ( k2_relat_1(sK5) = o_0_0_xboole_0 | k1_xboole_0 != o_0_0_xboole_0 ),
% 4.12/0.99      inference(superposition,[status(thm)],[c_10106,c_8767]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_1489,plain,
% 4.12/0.99      ( k2_enumset1(X0,X0,X0,X0) != X1
% 4.12/0.99      | k2_enumset1(X0,X0,X0,X0) = o_0_0_xboole_0
% 4.12/0.99      | o_0_0_xboole_0 != X1 ),
% 4.12/0.99      inference(instantiation,[status(thm)],[c_968]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_10607,plain,
% 4.12/0.99      ( k2_enumset1(X0,X0,X0,X0) != k2_relat_1(sK5)
% 4.12/0.99      | k2_enumset1(X0,X0,X0,X0) = o_0_0_xboole_0
% 4.12/0.99      | o_0_0_xboole_0 != k2_relat_1(sK5) ),
% 4.12/0.99      inference(instantiation,[status(thm)],[c_1489]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_10608,plain,
% 4.12/0.99      ( k2_enumset1(sK3,sK3,sK3,sK3) != k2_relat_1(sK5)
% 4.12/0.99      | k2_enumset1(sK3,sK3,sK3,sK3) = o_0_0_xboole_0
% 4.12/0.99      | o_0_0_xboole_0 != k2_relat_1(sK5) ),
% 4.12/0.99      inference(instantiation,[status(thm)],[c_10607]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_10897,plain,
% 4.12/0.99      ( r2_hidden(k1_funct_1(sK5,sK0(sK5,k2_enumset1(sK3,sK3,sK3,sK3))),k2_relat_1(sK5)) = iProver_top ),
% 4.12/0.99      inference(global_propositional_subsumption,
% 4.12/0.99                [status(thm)],
% 4.12/0.99                [c_10756,c_284,c_289,c_2069,c_3518,c_10122,c_10608]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_15,plain,
% 4.12/0.99      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 4.12/0.99      | r2_hidden(sK2(X1,X0),k1_relat_1(X1))
% 4.12/0.99      | ~ v1_funct_1(X1)
% 4.12/0.99      | ~ v1_relat_1(X1) ),
% 4.12/0.99      inference(cnf_transformation,[],[f89]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_367,plain,
% 4.12/0.99      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 4.12/0.99      | r2_hidden(sK2(X1,X0),k1_relat_1(X1))
% 4.12/0.99      | ~ v1_relat_1(X1)
% 4.12/0.99      | sK5 != X1 ),
% 4.12/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_27]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_368,plain,
% 4.12/0.99      ( ~ r2_hidden(X0,k2_relat_1(sK5))
% 4.12/0.99      | r2_hidden(sK2(sK5,X0),k1_relat_1(sK5))
% 4.12/0.99      | ~ v1_relat_1(sK5) ),
% 4.12/0.99      inference(unflattening,[status(thm)],[c_367]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_1345,plain,
% 4.12/0.99      ( r2_hidden(X0,k2_relat_1(sK5)) != iProver_top
% 4.12/0.99      | r2_hidden(sK2(sK5,X0),k1_relat_1(sK5)) = iProver_top
% 4.12/0.99      | v1_relat_1(sK5) != iProver_top ),
% 4.12/0.99      inference(predicate_to_equality,[status(thm)],[c_368]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_1473,plain,
% 4.12/0.99      ( r2_hidden(sK2(sK5,X0),k1_relat_1(sK5))
% 4.12/0.99      | ~ r2_hidden(X0,k2_relat_1(sK5)) ),
% 4.12/0.99      inference(global_propositional_subsumption,
% 4.12/0.99                [status(thm)],
% 4.12/0.99                [c_368,c_25,c_1445]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_1474,plain,
% 4.12/0.99      ( ~ r2_hidden(X0,k2_relat_1(sK5))
% 4.12/0.99      | r2_hidden(sK2(sK5,X0),k1_relat_1(sK5)) ),
% 4.12/0.99      inference(renaming,[status(thm)],[c_1473]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_1475,plain,
% 4.12/0.99      ( r2_hidden(X0,k2_relat_1(sK5)) != iProver_top
% 4.12/0.99      | r2_hidden(sK2(sK5,X0),k1_relat_1(sK5)) = iProver_top ),
% 4.12/0.99      inference(predicate_to_equality,[status(thm)],[c_1474]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_2411,plain,
% 4.12/0.99      ( r2_hidden(sK2(sK5,X0),k1_relat_1(sK5)) = iProver_top
% 4.12/0.99      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 4.12/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1345,c_1475]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_2412,plain,
% 4.12/0.99      ( r2_hidden(X0,k2_relat_1(sK5)) != iProver_top
% 4.12/0.99      | r2_hidden(sK2(sK5,X0),k1_relat_1(sK5)) = iProver_top ),
% 4.12/0.99      inference(renaming,[status(thm)],[c_2411]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_10219,plain,
% 4.12/0.99      ( r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 4.12/0.99      inference(superposition,[status(thm)],[c_2412,c_10209]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_10906,plain,
% 4.12/0.99      ( $false ),
% 4.12/0.99      inference(superposition,[status(thm)],[c_10897,c_10219]) ).
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 4.12/0.99  
% 4.12/0.99  ------                               Statistics
% 4.12/0.99  
% 4.12/0.99  ------ Selected
% 4.12/0.99  
% 4.12/0.99  total_time:                             0.465
% 4.12/0.99  
%------------------------------------------------------------------------------
