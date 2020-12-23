%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:04:49 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 528 expanded)
%              Number of clauses        :   70 ( 115 expanded)
%              Number of leaves         :   19 ( 129 expanded)
%              Depth                    :   21
%              Number of atoms          :  374 (1383 expanded)
%              Number of equality atoms :  139 ( 520 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f38,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( ~ r2_hidden(k1_funct_1(sK3,sK1),sK2)
      & k1_xboole_0 != sK2
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
      & v1_funct_2(sK3,k1_tarski(sK1),sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK1),sK2)
    & k1_xboole_0 != sK2
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
    & v1_funct_2(sK3,k1_tarski(sK1),sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f29,f38])).

fof(f66,plain,(
    v1_funct_2(sK3,k1_tarski(sK1),sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f8])).

fof(f70,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f47,f70])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f46,f71])).

fof(f73,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f45,f72])).

fof(f74,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f73])).

fof(f75,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f43,f74])).

fof(f80,plain,(
    v1_funct_2(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2) ),
    inference(definition_unfolding,[],[f66,f75])).

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
    inference(ennf_transformation,[],[f15])).

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

fof(f37,plain,(
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

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f67,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) ),
    inference(cnf_transformation,[],[f39])).

fof(f79,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2))) ),
    inference(definition_unfolding,[],[f67,f75])).

fof(f68,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f39])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f34])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f51,f74])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f65,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f69,plain,(
    ~ r2_hidden(k1_funct_1(sK3,sK1),sK2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_981,plain,
    ( r2_hidden(sK0(X0_48,X1_48),X0_48)
    | r1_tarski(X0_48,X1_48) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1222,plain,
    ( r2_hidden(sK0(X0_48,X1_48),X0_48) = iProver_top
    | r1_tarski(X0_48,X1_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_981])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_982,plain,
    ( ~ r2_hidden(sK0(X0_48,X1_48),X1_48)
    | r1_tarski(X0_48,X1_48) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1221,plain,
    ( r2_hidden(sK0(X0_48,X1_48),X1_48) != iProver_top
    | r1_tarski(X0_48,X1_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_982])).

cnf(c_1505,plain,
    ( r1_tarski(X0_48,X0_48) = iProver_top ),
    inference(superposition,[status(thm)],[c_1222,c_1221])).

cnf(c_21,negated_conjecture,
    ( v1_funct_2(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_323,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_20])).

cnf(c_324,plain,
    ( ~ v1_funct_2(sK3,X0,X1)
    | k1_relset_1(X0,X1,sK3) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_323])).

cnf(c_673,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != X0
    | k1_relset_1(X0,X1,sK3) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK2 != X1
    | sK3 != sK3
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_324])).

cnf(c_674,plain,
    ( k1_relset_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2,sK3) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2))
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_673])).

cnf(c_19,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_675,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2))
    | k1_relset_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2,sK3) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_674,c_19])).

cnf(c_676,plain,
    ( k1_relset_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2,sK3) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) ),
    inference(renaming,[status(thm)],[c_675])).

cnf(c_734,plain,
    ( k1_relset_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2,sK3) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(equality_resolution_simp,[status(thm)],[c_676])).

cnf(c_970,plain,
    ( k1_relset_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2,sK3) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(subtyping,[status(esa)],[c_734])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_359,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_20])).

cnf(c_360,plain,
    ( k1_relset_1(X0,X1,sK3) = k1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_359])).

cnf(c_973,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))
    | k1_relset_1(X0_48,X1_48,sK3) = k1_relat_1(sK3) ),
    inference(subtyping,[status(esa)],[c_360])).

cnf(c_1337,plain,
    ( k1_relset_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2,sK3) = k1_relat_1(sK3) ),
    inference(equality_resolution,[status(thm)],[c_973])).

cnf(c_1393,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k1_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_970,c_1337])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0),X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_978,plain,
    ( r2_hidden(X0_47,X0_48)
    | ~ r1_tarski(k6_enumset1(X1_47,X1_47,X1_47,X1_47,X1_47,X1_47,X1_47,X0_47),X0_48) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1225,plain,
    ( r2_hidden(X0_47,X0_48) = iProver_top
    | r1_tarski(k6_enumset1(X1_47,X1_47,X1_47,X1_47,X1_47,X1_47,X1_47,X0_47),X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_978])).

cnf(c_1603,plain,
    ( r2_hidden(sK1,X0_48) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0_48) != iProver_top ),
    inference(superposition,[status(thm)],[c_1393,c_1225])).

cnf(c_2228,plain,
    ( r2_hidden(sK1,k1_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1505,c_1603])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_980,plain,
    ( ~ r2_hidden(X0_47,X0_48)
    | r2_hidden(X0_47,X1_48)
    | ~ r1_tarski(X0_48,X1_48) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1424,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK1),X0_48)
    | r2_hidden(k1_funct_1(sK3,sK1),sK2)
    | ~ r1_tarski(X0_48,sK2) ),
    inference(instantiation,[status(thm)],[c_980])).

cnf(c_1994,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK1),k2_relat_1(sK3))
    | r2_hidden(k1_funct_1(sK3,sK1),sK2)
    | ~ r1_tarski(k2_relat_1(sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_1424])).

cnf(c_1995,plain,
    ( r2_hidden(k1_funct_1(sK3,sK1),k2_relat_1(sK3)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,sK1),sK2) = iProver_top
    | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1994])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_251,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_22])).

cnf(c_252,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_251])).

cnf(c_292,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(sK3))
    | r2_hidden(k1_funct_1(sK3,X3),k2_relat_1(sK3))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_252])).

cnf(c_293,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r2_hidden(X2,k1_relat_1(sK3))
    | r2_hidden(k1_funct_1(sK3,X2),k2_relat_1(sK3)) ),
    inference(unflattening,[status(thm)],[c_292])).

cnf(c_433,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3))
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_293])).

cnf(c_735,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3))
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
    inference(equality_resolution_simp,[status(thm)],[c_433])).

cnf(c_969,plain,
    ( ~ r2_hidden(X0_47,k1_relat_1(sK3))
    | r2_hidden(k1_funct_1(sK3,X0_47),k2_relat_1(sK3))
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)) ),
    inference(subtyping,[status(esa)],[c_735])).

cnf(c_983,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_969])).

cnf(c_1231,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_983])).

cnf(c_1870,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1231,c_1393])).

cnf(c_1876,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1870])).

cnf(c_7,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v5_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_271,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X3),X4)
    | ~ v1_relat_1(X3)
    | X0 != X3
    | X2 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_10])).

cnf(c_272,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_271])).

cnf(c_276,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_272,c_9])).

cnf(c_277,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_276])).

cnf(c_311,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X1))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_277,c_20])).

cnf(c_312,plain,
    ( r1_tarski(k2_relat_1(sK3),X0)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X0)) ),
    inference(unflattening,[status(thm)],[c_311])).

cnf(c_974,plain,
    ( r1_tarski(k2_relat_1(sK3),X0_48)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1_48,X0_48)) ),
    inference(subtyping,[status(esa)],[c_312])).

cnf(c_1373,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_974])).

cnf(c_1374,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2))
    | r1_tarski(k2_relat_1(sK3),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1373])).

cnf(c_989,plain,
    ( X0_49 = X0_49 ),
    theory(equality)).

cnf(c_1329,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) = k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_989])).

cnf(c_984,plain,
    ( ~ r2_hidden(X0_47,k1_relat_1(sK3))
    | r2_hidden(k1_funct_1(sK3,X0_47),k2_relat_1(sK3))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_969])).

cnf(c_1032,plain,
    ( r2_hidden(X0_47,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0_47),k2_relat_1(sK3)) = iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_984])).

cnf(c_1034,plain,
    ( r2_hidden(k1_funct_1(sK3,sK1),k2_relat_1(sK3)) = iProver_top
    | r2_hidden(sK1,k1_relat_1(sK3)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(instantiation,[status(thm)],[c_1032])).

cnf(c_985,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_969])).

cnf(c_1031,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_985])).

cnf(c_18,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(sK3,sK1),sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_26,plain,
    ( r2_hidden(k1_funct_1(sK3,sK1),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2228,c_1995,c_1876,c_1374,c_1329,c_1034,c_1031,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:06:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 1.99/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.00  
% 1.99/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.99/1.00  
% 1.99/1.00  ------  iProver source info
% 1.99/1.00  
% 1.99/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.99/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.99/1.00  git: non_committed_changes: false
% 1.99/1.00  git: last_make_outside_of_git: false
% 1.99/1.00  
% 1.99/1.00  ------ 
% 1.99/1.00  
% 1.99/1.00  ------ Input Options
% 1.99/1.00  
% 1.99/1.00  --out_options                           all
% 1.99/1.00  --tptp_safe_out                         true
% 1.99/1.00  --problem_path                          ""
% 1.99/1.00  --include_path                          ""
% 1.99/1.00  --clausifier                            res/vclausify_rel
% 1.99/1.00  --clausifier_options                    --mode clausify
% 1.99/1.00  --stdin                                 false
% 1.99/1.00  --stats_out                             all
% 1.99/1.00  
% 1.99/1.00  ------ General Options
% 1.99/1.00  
% 1.99/1.00  --fof                                   false
% 1.99/1.00  --time_out_real                         305.
% 1.99/1.00  --time_out_virtual                      -1.
% 1.99/1.00  --symbol_type_check                     false
% 1.99/1.00  --clausify_out                          false
% 1.99/1.00  --sig_cnt_out                           false
% 1.99/1.00  --trig_cnt_out                          false
% 1.99/1.00  --trig_cnt_out_tolerance                1.
% 1.99/1.00  --trig_cnt_out_sk_spl                   false
% 1.99/1.00  --abstr_cl_out                          false
% 1.99/1.00  
% 1.99/1.00  ------ Global Options
% 1.99/1.00  
% 1.99/1.00  --schedule                              default
% 1.99/1.00  --add_important_lit                     false
% 1.99/1.00  --prop_solver_per_cl                    1000
% 1.99/1.00  --min_unsat_core                        false
% 1.99/1.00  --soft_assumptions                      false
% 1.99/1.00  --soft_lemma_size                       3
% 1.99/1.00  --prop_impl_unit_size                   0
% 1.99/1.00  --prop_impl_unit                        []
% 1.99/1.00  --share_sel_clauses                     true
% 1.99/1.00  --reset_solvers                         false
% 1.99/1.00  --bc_imp_inh                            [conj_cone]
% 1.99/1.00  --conj_cone_tolerance                   3.
% 1.99/1.00  --extra_neg_conj                        none
% 1.99/1.00  --large_theory_mode                     true
% 1.99/1.00  --prolific_symb_bound                   200
% 1.99/1.00  --lt_threshold                          2000
% 1.99/1.00  --clause_weak_htbl                      true
% 1.99/1.00  --gc_record_bc_elim                     false
% 1.99/1.00  
% 1.99/1.00  ------ Preprocessing Options
% 1.99/1.00  
% 1.99/1.00  --preprocessing_flag                    true
% 1.99/1.00  --time_out_prep_mult                    0.1
% 1.99/1.00  --splitting_mode                        input
% 1.99/1.00  --splitting_grd                         true
% 1.99/1.00  --splitting_cvd                         false
% 1.99/1.00  --splitting_cvd_svl                     false
% 1.99/1.00  --splitting_nvd                         32
% 1.99/1.00  --sub_typing                            true
% 1.99/1.00  --prep_gs_sim                           true
% 1.99/1.00  --prep_unflatten                        true
% 1.99/1.00  --prep_res_sim                          true
% 1.99/1.00  --prep_upred                            true
% 1.99/1.00  --prep_sem_filter                       exhaustive
% 1.99/1.00  --prep_sem_filter_out                   false
% 1.99/1.00  --pred_elim                             true
% 1.99/1.00  --res_sim_input                         true
% 1.99/1.00  --eq_ax_congr_red                       true
% 1.99/1.00  --pure_diseq_elim                       true
% 1.99/1.00  --brand_transform                       false
% 1.99/1.00  --non_eq_to_eq                          false
% 1.99/1.00  --prep_def_merge                        true
% 1.99/1.00  --prep_def_merge_prop_impl              false
% 1.99/1.00  --prep_def_merge_mbd                    true
% 1.99/1.00  --prep_def_merge_tr_red                 false
% 1.99/1.00  --prep_def_merge_tr_cl                  false
% 1.99/1.00  --smt_preprocessing                     true
% 1.99/1.00  --smt_ac_axioms                         fast
% 1.99/1.00  --preprocessed_out                      false
% 1.99/1.00  --preprocessed_stats                    false
% 1.99/1.00  
% 1.99/1.00  ------ Abstraction refinement Options
% 1.99/1.00  
% 1.99/1.00  --abstr_ref                             []
% 1.99/1.00  --abstr_ref_prep                        false
% 1.99/1.00  --abstr_ref_until_sat                   false
% 1.99/1.00  --abstr_ref_sig_restrict                funpre
% 1.99/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.99/1.00  --abstr_ref_under                       []
% 1.99/1.00  
% 1.99/1.00  ------ SAT Options
% 1.99/1.00  
% 1.99/1.00  --sat_mode                              false
% 1.99/1.00  --sat_fm_restart_options                ""
% 1.99/1.00  --sat_gr_def                            false
% 1.99/1.00  --sat_epr_types                         true
% 1.99/1.00  --sat_non_cyclic_types                  false
% 1.99/1.00  --sat_finite_models                     false
% 1.99/1.00  --sat_fm_lemmas                         false
% 1.99/1.00  --sat_fm_prep                           false
% 1.99/1.00  --sat_fm_uc_incr                        true
% 1.99/1.00  --sat_out_model                         small
% 1.99/1.00  --sat_out_clauses                       false
% 1.99/1.00  
% 1.99/1.00  ------ QBF Options
% 1.99/1.00  
% 1.99/1.00  --qbf_mode                              false
% 1.99/1.00  --qbf_elim_univ                         false
% 1.99/1.00  --qbf_dom_inst                          none
% 1.99/1.00  --qbf_dom_pre_inst                      false
% 1.99/1.00  --qbf_sk_in                             false
% 1.99/1.00  --qbf_pred_elim                         true
% 1.99/1.00  --qbf_split                             512
% 1.99/1.00  
% 1.99/1.00  ------ BMC1 Options
% 1.99/1.00  
% 1.99/1.00  --bmc1_incremental                      false
% 1.99/1.00  --bmc1_axioms                           reachable_all
% 1.99/1.00  --bmc1_min_bound                        0
% 1.99/1.00  --bmc1_max_bound                        -1
% 1.99/1.00  --bmc1_max_bound_default                -1
% 1.99/1.00  --bmc1_symbol_reachability              true
% 1.99/1.00  --bmc1_property_lemmas                  false
% 1.99/1.00  --bmc1_k_induction                      false
% 1.99/1.00  --bmc1_non_equiv_states                 false
% 1.99/1.00  --bmc1_deadlock                         false
% 1.99/1.00  --bmc1_ucm                              false
% 1.99/1.00  --bmc1_add_unsat_core                   none
% 1.99/1.00  --bmc1_unsat_core_children              false
% 1.99/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.99/1.00  --bmc1_out_stat                         full
% 1.99/1.00  --bmc1_ground_init                      false
% 1.99/1.00  --bmc1_pre_inst_next_state              false
% 1.99/1.00  --bmc1_pre_inst_state                   false
% 1.99/1.00  --bmc1_pre_inst_reach_state             false
% 1.99/1.00  --bmc1_out_unsat_core                   false
% 1.99/1.00  --bmc1_aig_witness_out                  false
% 1.99/1.00  --bmc1_verbose                          false
% 1.99/1.00  --bmc1_dump_clauses_tptp                false
% 1.99/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.99/1.00  --bmc1_dump_file                        -
% 1.99/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.99/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.99/1.00  --bmc1_ucm_extend_mode                  1
% 1.99/1.00  --bmc1_ucm_init_mode                    2
% 1.99/1.00  --bmc1_ucm_cone_mode                    none
% 1.99/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.99/1.00  --bmc1_ucm_relax_model                  4
% 1.99/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.99/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.99/1.00  --bmc1_ucm_layered_model                none
% 1.99/1.00  --bmc1_ucm_max_lemma_size               10
% 1.99/1.00  
% 1.99/1.00  ------ AIG Options
% 1.99/1.00  
% 1.99/1.00  --aig_mode                              false
% 1.99/1.00  
% 1.99/1.00  ------ Instantiation Options
% 1.99/1.00  
% 1.99/1.00  --instantiation_flag                    true
% 1.99/1.00  --inst_sos_flag                         false
% 1.99/1.00  --inst_sos_phase                        true
% 1.99/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.99/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.99/1.00  --inst_lit_sel_side                     num_symb
% 1.99/1.00  --inst_solver_per_active                1400
% 1.99/1.00  --inst_solver_calls_frac                1.
% 1.99/1.00  --inst_passive_queue_type               priority_queues
% 1.99/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.99/1.00  --inst_passive_queues_freq              [25;2]
% 1.99/1.00  --inst_dismatching                      true
% 1.99/1.00  --inst_eager_unprocessed_to_passive     true
% 1.99/1.00  --inst_prop_sim_given                   true
% 1.99/1.00  --inst_prop_sim_new                     false
% 1.99/1.00  --inst_subs_new                         false
% 1.99/1.00  --inst_eq_res_simp                      false
% 1.99/1.00  --inst_subs_given                       false
% 1.99/1.00  --inst_orphan_elimination               true
% 1.99/1.00  --inst_learning_loop_flag               true
% 1.99/1.00  --inst_learning_start                   3000
% 1.99/1.00  --inst_learning_factor                  2
% 1.99/1.00  --inst_start_prop_sim_after_learn       3
% 1.99/1.00  --inst_sel_renew                        solver
% 1.99/1.00  --inst_lit_activity_flag                true
% 1.99/1.00  --inst_restr_to_given                   false
% 1.99/1.00  --inst_activity_threshold               500
% 1.99/1.00  --inst_out_proof                        true
% 1.99/1.00  
% 1.99/1.00  ------ Resolution Options
% 1.99/1.00  
% 1.99/1.00  --resolution_flag                       true
% 1.99/1.00  --res_lit_sel                           adaptive
% 1.99/1.00  --res_lit_sel_side                      none
% 1.99/1.00  --res_ordering                          kbo
% 1.99/1.00  --res_to_prop_solver                    active
% 1.99/1.00  --res_prop_simpl_new                    false
% 1.99/1.00  --res_prop_simpl_given                  true
% 1.99/1.00  --res_passive_queue_type                priority_queues
% 1.99/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.99/1.00  --res_passive_queues_freq               [15;5]
% 1.99/1.00  --res_forward_subs                      full
% 1.99/1.00  --res_backward_subs                     full
% 1.99/1.00  --res_forward_subs_resolution           true
% 1.99/1.00  --res_backward_subs_resolution          true
% 1.99/1.00  --res_orphan_elimination                true
% 1.99/1.00  --res_time_limit                        2.
% 1.99/1.00  --res_out_proof                         true
% 1.99/1.00  
% 1.99/1.00  ------ Superposition Options
% 1.99/1.00  
% 1.99/1.00  --superposition_flag                    true
% 1.99/1.00  --sup_passive_queue_type                priority_queues
% 1.99/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.99/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.99/1.00  --demod_completeness_check              fast
% 1.99/1.00  --demod_use_ground                      true
% 1.99/1.00  --sup_to_prop_solver                    passive
% 1.99/1.00  --sup_prop_simpl_new                    true
% 1.99/1.00  --sup_prop_simpl_given                  true
% 1.99/1.00  --sup_fun_splitting                     false
% 1.99/1.00  --sup_smt_interval                      50000
% 1.99/1.00  
% 1.99/1.00  ------ Superposition Simplification Setup
% 1.99/1.00  
% 1.99/1.00  --sup_indices_passive                   []
% 1.99/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.99/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/1.00  --sup_full_bw                           [BwDemod]
% 1.99/1.00  --sup_immed_triv                        [TrivRules]
% 1.99/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.99/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/1.00  --sup_immed_bw_main                     []
% 1.99/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.99/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.99/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.99/1.00  
% 1.99/1.00  ------ Combination Options
% 1.99/1.00  
% 1.99/1.00  --comb_res_mult                         3
% 1.99/1.00  --comb_sup_mult                         2
% 1.99/1.00  --comb_inst_mult                        10
% 1.99/1.00  
% 1.99/1.00  ------ Debug Options
% 1.99/1.00  
% 1.99/1.00  --dbg_backtrace                         false
% 1.99/1.00  --dbg_dump_prop_clauses                 false
% 1.99/1.00  --dbg_dump_prop_clauses_file            -
% 1.99/1.00  --dbg_out_stat                          false
% 1.99/1.00  ------ Parsing...
% 1.99/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.99/1.00  
% 1.99/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 1.99/1.00  
% 1.99/1.00  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.99/1.00  
% 1.99/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.99/1.00  ------ Proving...
% 1.99/1.00  ------ Problem Properties 
% 1.99/1.00  
% 1.99/1.00  
% 1.99/1.00  clauses                                 16
% 1.99/1.00  conjectures                             2
% 1.99/1.00  EPR                                     3
% 1.99/1.00  Horn                                    13
% 1.99/1.00  unary                                   3
% 1.99/1.00  binary                                  8
% 1.99/1.00  lits                                    35
% 1.99/1.00  lits eq                                 13
% 1.99/1.00  fd_pure                                 0
% 1.99/1.00  fd_pseudo                               0
% 1.99/1.00  fd_cond                                 0
% 1.99/1.00  fd_pseudo_cond                          0
% 1.99/1.00  AC symbols                              0
% 1.99/1.00  
% 1.99/1.00  ------ Schedule dynamic 5 is on 
% 1.99/1.00  
% 1.99/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.99/1.00  
% 1.99/1.00  
% 1.99/1.00  ------ 
% 1.99/1.00  Current options:
% 1.99/1.00  ------ 
% 1.99/1.00  
% 1.99/1.00  ------ Input Options
% 1.99/1.00  
% 1.99/1.00  --out_options                           all
% 1.99/1.00  --tptp_safe_out                         true
% 1.99/1.00  --problem_path                          ""
% 1.99/1.00  --include_path                          ""
% 1.99/1.00  --clausifier                            res/vclausify_rel
% 1.99/1.00  --clausifier_options                    --mode clausify
% 1.99/1.00  --stdin                                 false
% 1.99/1.00  --stats_out                             all
% 1.99/1.00  
% 1.99/1.00  ------ General Options
% 1.99/1.00  
% 1.99/1.00  --fof                                   false
% 1.99/1.00  --time_out_real                         305.
% 1.99/1.00  --time_out_virtual                      -1.
% 1.99/1.00  --symbol_type_check                     false
% 1.99/1.00  --clausify_out                          false
% 1.99/1.00  --sig_cnt_out                           false
% 1.99/1.00  --trig_cnt_out                          false
% 1.99/1.00  --trig_cnt_out_tolerance                1.
% 1.99/1.00  --trig_cnt_out_sk_spl                   false
% 1.99/1.00  --abstr_cl_out                          false
% 1.99/1.00  
% 1.99/1.00  ------ Global Options
% 1.99/1.00  
% 1.99/1.00  --schedule                              default
% 1.99/1.00  --add_important_lit                     false
% 1.99/1.00  --prop_solver_per_cl                    1000
% 1.99/1.00  --min_unsat_core                        false
% 1.99/1.00  --soft_assumptions                      false
% 1.99/1.00  --soft_lemma_size                       3
% 1.99/1.00  --prop_impl_unit_size                   0
% 1.99/1.00  --prop_impl_unit                        []
% 1.99/1.00  --share_sel_clauses                     true
% 1.99/1.00  --reset_solvers                         false
% 1.99/1.00  --bc_imp_inh                            [conj_cone]
% 1.99/1.00  --conj_cone_tolerance                   3.
% 1.99/1.00  --extra_neg_conj                        none
% 1.99/1.00  --large_theory_mode                     true
% 1.99/1.00  --prolific_symb_bound                   200
% 1.99/1.00  --lt_threshold                          2000
% 1.99/1.00  --clause_weak_htbl                      true
% 1.99/1.00  --gc_record_bc_elim                     false
% 1.99/1.00  
% 1.99/1.00  ------ Preprocessing Options
% 1.99/1.00  
% 1.99/1.00  --preprocessing_flag                    true
% 1.99/1.00  --time_out_prep_mult                    0.1
% 1.99/1.00  --splitting_mode                        input
% 1.99/1.00  --splitting_grd                         true
% 1.99/1.00  --splitting_cvd                         false
% 1.99/1.00  --splitting_cvd_svl                     false
% 1.99/1.00  --splitting_nvd                         32
% 1.99/1.00  --sub_typing                            true
% 1.99/1.00  --prep_gs_sim                           true
% 1.99/1.00  --prep_unflatten                        true
% 1.99/1.00  --prep_res_sim                          true
% 1.99/1.00  --prep_upred                            true
% 1.99/1.00  --prep_sem_filter                       exhaustive
% 1.99/1.00  --prep_sem_filter_out                   false
% 1.99/1.00  --pred_elim                             true
% 1.99/1.00  --res_sim_input                         true
% 1.99/1.00  --eq_ax_congr_red                       true
% 1.99/1.00  --pure_diseq_elim                       true
% 1.99/1.00  --brand_transform                       false
% 1.99/1.00  --non_eq_to_eq                          false
% 1.99/1.00  --prep_def_merge                        true
% 1.99/1.00  --prep_def_merge_prop_impl              false
% 1.99/1.00  --prep_def_merge_mbd                    true
% 1.99/1.00  --prep_def_merge_tr_red                 false
% 1.99/1.00  --prep_def_merge_tr_cl                  false
% 1.99/1.00  --smt_preprocessing                     true
% 1.99/1.00  --smt_ac_axioms                         fast
% 1.99/1.00  --preprocessed_out                      false
% 1.99/1.00  --preprocessed_stats                    false
% 1.99/1.00  
% 1.99/1.00  ------ Abstraction refinement Options
% 1.99/1.00  
% 1.99/1.00  --abstr_ref                             []
% 1.99/1.00  --abstr_ref_prep                        false
% 1.99/1.00  --abstr_ref_until_sat                   false
% 1.99/1.00  --abstr_ref_sig_restrict                funpre
% 1.99/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.99/1.00  --abstr_ref_under                       []
% 1.99/1.00  
% 1.99/1.00  ------ SAT Options
% 1.99/1.00  
% 1.99/1.00  --sat_mode                              false
% 1.99/1.00  --sat_fm_restart_options                ""
% 1.99/1.00  --sat_gr_def                            false
% 1.99/1.00  --sat_epr_types                         true
% 1.99/1.00  --sat_non_cyclic_types                  false
% 1.99/1.00  --sat_finite_models                     false
% 1.99/1.00  --sat_fm_lemmas                         false
% 1.99/1.00  --sat_fm_prep                           false
% 1.99/1.00  --sat_fm_uc_incr                        true
% 1.99/1.00  --sat_out_model                         small
% 1.99/1.00  --sat_out_clauses                       false
% 1.99/1.00  
% 1.99/1.00  ------ QBF Options
% 1.99/1.00  
% 1.99/1.00  --qbf_mode                              false
% 1.99/1.00  --qbf_elim_univ                         false
% 1.99/1.00  --qbf_dom_inst                          none
% 1.99/1.00  --qbf_dom_pre_inst                      false
% 1.99/1.00  --qbf_sk_in                             false
% 1.99/1.00  --qbf_pred_elim                         true
% 1.99/1.00  --qbf_split                             512
% 1.99/1.00  
% 1.99/1.00  ------ BMC1 Options
% 1.99/1.00  
% 1.99/1.00  --bmc1_incremental                      false
% 1.99/1.00  --bmc1_axioms                           reachable_all
% 1.99/1.00  --bmc1_min_bound                        0
% 1.99/1.00  --bmc1_max_bound                        -1
% 1.99/1.00  --bmc1_max_bound_default                -1
% 1.99/1.00  --bmc1_symbol_reachability              true
% 1.99/1.00  --bmc1_property_lemmas                  false
% 1.99/1.00  --bmc1_k_induction                      false
% 1.99/1.00  --bmc1_non_equiv_states                 false
% 1.99/1.00  --bmc1_deadlock                         false
% 1.99/1.00  --bmc1_ucm                              false
% 1.99/1.00  --bmc1_add_unsat_core                   none
% 1.99/1.00  --bmc1_unsat_core_children              false
% 1.99/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.99/1.00  --bmc1_out_stat                         full
% 1.99/1.00  --bmc1_ground_init                      false
% 1.99/1.00  --bmc1_pre_inst_next_state              false
% 1.99/1.00  --bmc1_pre_inst_state                   false
% 1.99/1.00  --bmc1_pre_inst_reach_state             false
% 1.99/1.00  --bmc1_out_unsat_core                   false
% 1.99/1.00  --bmc1_aig_witness_out                  false
% 1.99/1.00  --bmc1_verbose                          false
% 1.99/1.00  --bmc1_dump_clauses_tptp                false
% 1.99/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.99/1.00  --bmc1_dump_file                        -
% 1.99/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.99/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.99/1.00  --bmc1_ucm_extend_mode                  1
% 1.99/1.00  --bmc1_ucm_init_mode                    2
% 1.99/1.00  --bmc1_ucm_cone_mode                    none
% 1.99/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.99/1.00  --bmc1_ucm_relax_model                  4
% 1.99/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.99/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.99/1.00  --bmc1_ucm_layered_model                none
% 1.99/1.00  --bmc1_ucm_max_lemma_size               10
% 1.99/1.00  
% 1.99/1.00  ------ AIG Options
% 1.99/1.00  
% 1.99/1.00  --aig_mode                              false
% 1.99/1.00  
% 1.99/1.00  ------ Instantiation Options
% 1.99/1.00  
% 1.99/1.00  --instantiation_flag                    true
% 1.99/1.00  --inst_sos_flag                         false
% 1.99/1.00  --inst_sos_phase                        true
% 1.99/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.99/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.99/1.00  --inst_lit_sel_side                     none
% 1.99/1.00  --inst_solver_per_active                1400
% 1.99/1.00  --inst_solver_calls_frac                1.
% 1.99/1.00  --inst_passive_queue_type               priority_queues
% 1.99/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.99/1.00  --inst_passive_queues_freq              [25;2]
% 1.99/1.00  --inst_dismatching                      true
% 1.99/1.00  --inst_eager_unprocessed_to_passive     true
% 1.99/1.00  --inst_prop_sim_given                   true
% 1.99/1.00  --inst_prop_sim_new                     false
% 1.99/1.00  --inst_subs_new                         false
% 1.99/1.00  --inst_eq_res_simp                      false
% 1.99/1.00  --inst_subs_given                       false
% 1.99/1.00  --inst_orphan_elimination               true
% 1.99/1.00  --inst_learning_loop_flag               true
% 1.99/1.00  --inst_learning_start                   3000
% 1.99/1.00  --inst_learning_factor                  2
% 1.99/1.00  --inst_start_prop_sim_after_learn       3
% 1.99/1.00  --inst_sel_renew                        solver
% 1.99/1.00  --inst_lit_activity_flag                true
% 1.99/1.00  --inst_restr_to_given                   false
% 1.99/1.00  --inst_activity_threshold               500
% 1.99/1.00  --inst_out_proof                        true
% 1.99/1.00  
% 1.99/1.00  ------ Resolution Options
% 1.99/1.00  
% 1.99/1.00  --resolution_flag                       false
% 1.99/1.00  --res_lit_sel                           adaptive
% 1.99/1.00  --res_lit_sel_side                      none
% 1.99/1.00  --res_ordering                          kbo
% 1.99/1.00  --res_to_prop_solver                    active
% 1.99/1.00  --res_prop_simpl_new                    false
% 1.99/1.00  --res_prop_simpl_given                  true
% 1.99/1.00  --res_passive_queue_type                priority_queues
% 1.99/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.99/1.00  --res_passive_queues_freq               [15;5]
% 1.99/1.00  --res_forward_subs                      full
% 1.99/1.00  --res_backward_subs                     full
% 1.99/1.00  --res_forward_subs_resolution           true
% 1.99/1.00  --res_backward_subs_resolution          true
% 1.99/1.00  --res_orphan_elimination                true
% 1.99/1.00  --res_time_limit                        2.
% 1.99/1.00  --res_out_proof                         true
% 1.99/1.00  
% 1.99/1.00  ------ Superposition Options
% 1.99/1.00  
% 1.99/1.00  --superposition_flag                    true
% 1.99/1.00  --sup_passive_queue_type                priority_queues
% 1.99/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.99/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.99/1.00  --demod_completeness_check              fast
% 1.99/1.00  --demod_use_ground                      true
% 1.99/1.00  --sup_to_prop_solver                    passive
% 1.99/1.00  --sup_prop_simpl_new                    true
% 1.99/1.00  --sup_prop_simpl_given                  true
% 1.99/1.00  --sup_fun_splitting                     false
% 1.99/1.00  --sup_smt_interval                      50000
% 1.99/1.00  
% 1.99/1.00  ------ Superposition Simplification Setup
% 1.99/1.00  
% 1.99/1.00  --sup_indices_passive                   []
% 1.99/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.99/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/1.00  --sup_full_bw                           [BwDemod]
% 1.99/1.00  --sup_immed_triv                        [TrivRules]
% 1.99/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.99/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/1.00  --sup_immed_bw_main                     []
% 1.99/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.99/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.99/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.99/1.00  
% 1.99/1.00  ------ Combination Options
% 1.99/1.00  
% 1.99/1.00  --comb_res_mult                         3
% 1.99/1.00  --comb_sup_mult                         2
% 1.99/1.00  --comb_inst_mult                        10
% 1.99/1.00  
% 1.99/1.00  ------ Debug Options
% 1.99/1.00  
% 1.99/1.00  --dbg_backtrace                         false
% 1.99/1.00  --dbg_dump_prop_clauses                 false
% 1.99/1.00  --dbg_dump_prop_clauses_file            -
% 1.99/1.00  --dbg_out_stat                          false
% 1.99/1.00  
% 1.99/1.00  
% 1.99/1.00  
% 1.99/1.00  
% 1.99/1.00  ------ Proving...
% 1.99/1.00  
% 1.99/1.00  
% 1.99/1.00  % SZS status Theorem for theBenchmark.p
% 1.99/1.00  
% 1.99/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.99/1.00  
% 1.99/1.00  fof(f1,axiom,(
% 1.99/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.99/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.00  
% 1.99/1.00  fof(f19,plain,(
% 1.99/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.99/1.00    inference(ennf_transformation,[],[f1])).
% 1.99/1.00  
% 1.99/1.00  fof(f30,plain,(
% 1.99/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.99/1.00    inference(nnf_transformation,[],[f19])).
% 1.99/1.00  
% 1.99/1.00  fof(f31,plain,(
% 1.99/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.99/1.00    inference(rectify,[],[f30])).
% 1.99/1.00  
% 1.99/1.00  fof(f32,plain,(
% 1.99/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 1.99/1.00    introduced(choice_axiom,[])).
% 1.99/1.00  
% 1.99/1.00  fof(f33,plain,(
% 1.99/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.99/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).
% 1.99/1.00  
% 1.99/1.00  fof(f41,plain,(
% 1.99/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 1.99/1.00    inference(cnf_transformation,[],[f33])).
% 1.99/1.00  
% 1.99/1.00  fof(f42,plain,(
% 1.99/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 1.99/1.00    inference(cnf_transformation,[],[f33])).
% 1.99/1.00  
% 1.99/1.00  fof(f16,conjecture,(
% 1.99/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 1.99/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.00  
% 1.99/1.00  fof(f17,negated_conjecture,(
% 1.99/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 1.99/1.00    inference(negated_conjecture,[],[f16])).
% 1.99/1.00  
% 1.99/1.00  fof(f28,plain,(
% 1.99/1.00    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 1.99/1.00    inference(ennf_transformation,[],[f17])).
% 1.99/1.00  
% 1.99/1.00  fof(f29,plain,(
% 1.99/1.00    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 1.99/1.00    inference(flattening,[],[f28])).
% 1.99/1.00  
% 1.99/1.00  fof(f38,plain,(
% 1.99/1.00    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (~r2_hidden(k1_funct_1(sK3,sK1),sK2) & k1_xboole_0 != sK2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK3,k1_tarski(sK1),sK2) & v1_funct_1(sK3))),
% 1.99/1.00    introduced(choice_axiom,[])).
% 1.99/1.00  
% 1.99/1.00  fof(f39,plain,(
% 1.99/1.00    ~r2_hidden(k1_funct_1(sK3,sK1),sK2) & k1_xboole_0 != sK2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK3,k1_tarski(sK1),sK2) & v1_funct_1(sK3)),
% 1.99/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f29,f38])).
% 1.99/1.00  
% 1.99/1.00  fof(f66,plain,(
% 1.99/1.00    v1_funct_2(sK3,k1_tarski(sK1),sK2)),
% 1.99/1.00    inference(cnf_transformation,[],[f39])).
% 1.99/1.00  
% 1.99/1.00  fof(f2,axiom,(
% 1.99/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.99/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.00  
% 1.99/1.00  fof(f43,plain,(
% 1.99/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.99/1.00    inference(cnf_transformation,[],[f2])).
% 1.99/1.00  
% 1.99/1.00  fof(f3,axiom,(
% 1.99/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.99/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.00  
% 1.99/1.00  fof(f44,plain,(
% 1.99/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.99/1.00    inference(cnf_transformation,[],[f3])).
% 1.99/1.00  
% 1.99/1.00  fof(f4,axiom,(
% 1.99/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.99/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.00  
% 1.99/1.00  fof(f45,plain,(
% 1.99/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.99/1.00    inference(cnf_transformation,[],[f4])).
% 1.99/1.00  
% 1.99/1.00  fof(f5,axiom,(
% 1.99/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.99/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.00  
% 1.99/1.00  fof(f46,plain,(
% 1.99/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.99/1.00    inference(cnf_transformation,[],[f5])).
% 1.99/1.00  
% 1.99/1.00  fof(f6,axiom,(
% 1.99/1.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 1.99/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.00  
% 1.99/1.00  fof(f47,plain,(
% 1.99/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 1.99/1.00    inference(cnf_transformation,[],[f6])).
% 1.99/1.00  
% 1.99/1.00  fof(f7,axiom,(
% 1.99/1.00    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 1.99/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.00  
% 1.99/1.00  fof(f48,plain,(
% 1.99/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 1.99/1.00    inference(cnf_transformation,[],[f7])).
% 1.99/1.00  
% 1.99/1.00  fof(f8,axiom,(
% 1.99/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 1.99/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.00  
% 1.99/1.00  fof(f49,plain,(
% 1.99/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 1.99/1.00    inference(cnf_transformation,[],[f8])).
% 1.99/1.00  
% 1.99/1.00  fof(f70,plain,(
% 1.99/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.99/1.00    inference(definition_unfolding,[],[f48,f49])).
% 1.99/1.00  
% 1.99/1.00  fof(f71,plain,(
% 1.99/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.99/1.00    inference(definition_unfolding,[],[f47,f70])).
% 1.99/1.00  
% 1.99/1.00  fof(f72,plain,(
% 1.99/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.99/1.00    inference(definition_unfolding,[],[f46,f71])).
% 1.99/1.00  
% 1.99/1.00  fof(f73,plain,(
% 1.99/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.99/1.00    inference(definition_unfolding,[],[f45,f72])).
% 1.99/1.00  
% 1.99/1.00  fof(f74,plain,(
% 1.99/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.99/1.00    inference(definition_unfolding,[],[f44,f73])).
% 1.99/1.00  
% 1.99/1.00  fof(f75,plain,(
% 1.99/1.00    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.99/1.00    inference(definition_unfolding,[],[f43,f74])).
% 1.99/1.00  
% 1.99/1.00  fof(f80,plain,(
% 1.99/1.00    v1_funct_2(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)),
% 1.99/1.00    inference(definition_unfolding,[],[f66,f75])).
% 1.99/1.00  
% 1.99/1.00  fof(f15,axiom,(
% 1.99/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.99/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.00  
% 1.99/1.00  fof(f26,plain,(
% 1.99/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.99/1.00    inference(ennf_transformation,[],[f15])).
% 1.99/1.00  
% 1.99/1.00  fof(f27,plain,(
% 1.99/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.99/1.00    inference(flattening,[],[f26])).
% 1.99/1.00  
% 1.99/1.00  fof(f37,plain,(
% 1.99/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.99/1.00    inference(nnf_transformation,[],[f27])).
% 1.99/1.00  
% 1.99/1.00  fof(f59,plain,(
% 1.99/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.99/1.00    inference(cnf_transformation,[],[f37])).
% 1.99/1.00  
% 1.99/1.00  fof(f67,plain,(
% 1.99/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))),
% 1.99/1.00    inference(cnf_transformation,[],[f39])).
% 1.99/1.00  
% 1.99/1.00  fof(f79,plain,(
% 1.99/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)))),
% 1.99/1.00    inference(definition_unfolding,[],[f67,f75])).
% 1.99/1.00  
% 1.99/1.00  fof(f68,plain,(
% 1.99/1.00    k1_xboole_0 != sK2),
% 1.99/1.00    inference(cnf_transformation,[],[f39])).
% 1.99/1.00  
% 1.99/1.00  fof(f14,axiom,(
% 1.99/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.99/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.00  
% 1.99/1.00  fof(f25,plain,(
% 1.99/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.99/1.00    inference(ennf_transformation,[],[f14])).
% 1.99/1.00  
% 1.99/1.00  fof(f58,plain,(
% 1.99/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.99/1.00    inference(cnf_transformation,[],[f25])).
% 1.99/1.00  
% 1.99/1.00  fof(f9,axiom,(
% 1.99/1.00    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.99/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.00  
% 1.99/1.00  fof(f34,plain,(
% 1.99/1.00    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.99/1.00    inference(nnf_transformation,[],[f9])).
% 1.99/1.00  
% 1.99/1.00  fof(f35,plain,(
% 1.99/1.00    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.99/1.00    inference(flattening,[],[f34])).
% 1.99/1.00  
% 1.99/1.00  fof(f51,plain,(
% 1.99/1.00    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 1.99/1.00    inference(cnf_transformation,[],[f35])).
% 1.99/1.00  
% 1.99/1.00  fof(f77,plain,(
% 1.99/1.00    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)) )),
% 1.99/1.00    inference(definition_unfolding,[],[f51,f74])).
% 1.99/1.00  
% 1.99/1.00  fof(f40,plain,(
% 1.99/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.99/1.00    inference(cnf_transformation,[],[f33])).
% 1.99/1.00  
% 1.99/1.00  fof(f12,axiom,(
% 1.99/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.99/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.00  
% 1.99/1.00  fof(f23,plain,(
% 1.99/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.99/1.00    inference(ennf_transformation,[],[f12])).
% 1.99/1.00  
% 1.99/1.00  fof(f56,plain,(
% 1.99/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.99/1.00    inference(cnf_transformation,[],[f23])).
% 1.99/1.00  
% 1.99/1.00  fof(f11,axiom,(
% 1.99/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 1.99/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.00  
% 1.99/1.00  fof(f21,plain,(
% 1.99/1.00    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.99/1.00    inference(ennf_transformation,[],[f11])).
% 1.99/1.00  
% 1.99/1.00  fof(f22,plain,(
% 1.99/1.00    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.99/1.00    inference(flattening,[],[f21])).
% 1.99/1.00  
% 1.99/1.00  fof(f55,plain,(
% 1.99/1.00    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.99/1.00    inference(cnf_transformation,[],[f22])).
% 1.99/1.00  
% 1.99/1.00  fof(f65,plain,(
% 1.99/1.00    v1_funct_1(sK3)),
% 1.99/1.00    inference(cnf_transformation,[],[f39])).
% 1.99/1.00  
% 1.99/1.00  fof(f10,axiom,(
% 1.99/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.99/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.00  
% 1.99/1.00  fof(f20,plain,(
% 1.99/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.99/1.00    inference(ennf_transformation,[],[f10])).
% 1.99/1.00  
% 1.99/1.00  fof(f36,plain,(
% 1.99/1.00    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.99/1.00    inference(nnf_transformation,[],[f20])).
% 1.99/1.00  
% 1.99/1.00  fof(f53,plain,(
% 1.99/1.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.99/1.00    inference(cnf_transformation,[],[f36])).
% 1.99/1.00  
% 1.99/1.00  fof(f13,axiom,(
% 1.99/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.99/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.00  
% 1.99/1.00  fof(f18,plain,(
% 1.99/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.99/1.00    inference(pure_predicate_removal,[],[f13])).
% 1.99/1.00  
% 1.99/1.00  fof(f24,plain,(
% 1.99/1.00    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.99/1.00    inference(ennf_transformation,[],[f18])).
% 1.99/1.00  
% 1.99/1.00  fof(f57,plain,(
% 1.99/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.99/1.00    inference(cnf_transformation,[],[f24])).
% 1.99/1.00  
% 1.99/1.00  fof(f69,plain,(
% 1.99/1.00    ~r2_hidden(k1_funct_1(sK3,sK1),sK2)),
% 1.99/1.00    inference(cnf_transformation,[],[f39])).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1,plain,
% 1.99/1.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 1.99/1.00      inference(cnf_transformation,[],[f41]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_981,plain,
% 1.99/1.00      ( r2_hidden(sK0(X0_48,X1_48),X0_48) | r1_tarski(X0_48,X1_48) ),
% 1.99/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1222,plain,
% 1.99/1.00      ( r2_hidden(sK0(X0_48,X1_48),X0_48) = iProver_top
% 1.99/1.00      | r1_tarski(X0_48,X1_48) = iProver_top ),
% 1.99/1.00      inference(predicate_to_equality,[status(thm)],[c_981]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_0,plain,
% 1.99/1.00      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 1.99/1.00      inference(cnf_transformation,[],[f42]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_982,plain,
% 1.99/1.00      ( ~ r2_hidden(sK0(X0_48,X1_48),X1_48) | r1_tarski(X0_48,X1_48) ),
% 1.99/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1221,plain,
% 1.99/1.00      ( r2_hidden(sK0(X0_48,X1_48),X1_48) != iProver_top
% 1.99/1.00      | r1_tarski(X0_48,X1_48) = iProver_top ),
% 1.99/1.00      inference(predicate_to_equality,[status(thm)],[c_982]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1505,plain,
% 1.99/1.00      ( r1_tarski(X0_48,X0_48) = iProver_top ),
% 1.99/1.00      inference(superposition,[status(thm)],[c_1222,c_1221]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_21,negated_conjecture,
% 1.99/1.00      ( v1_funct_2(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2) ),
% 1.99/1.00      inference(cnf_transformation,[],[f80]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_17,plain,
% 1.99/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 1.99/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.99/1.00      | k1_relset_1(X1,X2,X0) = X1
% 1.99/1.00      | k1_xboole_0 = X2 ),
% 1.99/1.00      inference(cnf_transformation,[],[f59]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_20,negated_conjecture,
% 1.99/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2))) ),
% 1.99/1.00      inference(cnf_transformation,[],[f79]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_323,plain,
% 1.99/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 1.99/1.00      | k1_relset_1(X1,X2,X0) = X1
% 1.99/1.00      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 1.99/1.00      | sK3 != X0
% 1.99/1.00      | k1_xboole_0 = X2 ),
% 1.99/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_20]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_324,plain,
% 1.99/1.00      ( ~ v1_funct_2(sK3,X0,X1)
% 1.99/1.00      | k1_relset_1(X0,X1,sK3) = X0
% 1.99/1.00      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.99/1.00      | k1_xboole_0 = X1 ),
% 1.99/1.00      inference(unflattening,[status(thm)],[c_323]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_673,plain,
% 1.99/1.00      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != X0
% 1.99/1.00      | k1_relset_1(X0,X1,sK3) = X0
% 1.99/1.00      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.99/1.00      | sK2 != X1
% 1.99/1.00      | sK3 != sK3
% 1.99/1.00      | k1_xboole_0 = X1 ),
% 1.99/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_324]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_674,plain,
% 1.99/1.00      ( k1_relset_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2,sK3) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
% 1.99/1.00      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2))
% 1.99/1.00      | k1_xboole_0 = sK2 ),
% 1.99/1.00      inference(unflattening,[status(thm)],[c_673]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_19,negated_conjecture,
% 1.99/1.00      ( k1_xboole_0 != sK2 ),
% 1.99/1.00      inference(cnf_transformation,[],[f68]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_675,plain,
% 1.99/1.00      ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2))
% 1.99/1.00      | k1_relset_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2,sK3) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
% 1.99/1.00      inference(global_propositional_subsumption,
% 1.99/1.00                [status(thm)],
% 1.99/1.00                [c_674,c_19]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_676,plain,
% 1.99/1.00      ( k1_relset_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2,sK3) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
% 1.99/1.00      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) ),
% 1.99/1.00      inference(renaming,[status(thm)],[c_675]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_734,plain,
% 1.99/1.00      ( k1_relset_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2,sK3) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
% 1.99/1.00      inference(equality_resolution_simp,[status(thm)],[c_676]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_970,plain,
% 1.99/1.00      ( k1_relset_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2,sK3) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
% 1.99/1.00      inference(subtyping,[status(esa)],[c_734]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_11,plain,
% 1.99/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.99/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 1.99/1.00      inference(cnf_transformation,[],[f58]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_359,plain,
% 1.99/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 1.99/1.00      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.99/1.00      | sK3 != X2 ),
% 1.99/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_20]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_360,plain,
% 1.99/1.00      ( k1_relset_1(X0,X1,sK3) = k1_relat_1(sK3)
% 1.99/1.00      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 1.99/1.01      inference(unflattening,[status(thm)],[c_359]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_973,plain,
% 1.99/1.01      ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))
% 1.99/1.01      | k1_relset_1(X0_48,X1_48,sK3) = k1_relat_1(sK3) ),
% 1.99/1.01      inference(subtyping,[status(esa)],[c_360]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_1337,plain,
% 1.99/1.01      ( k1_relset_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2,sK3) = k1_relat_1(sK3) ),
% 1.99/1.01      inference(equality_resolution,[status(thm)],[c_973]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_1393,plain,
% 1.99/1.01      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k1_relat_1(sK3) ),
% 1.99/1.01      inference(light_normalisation,[status(thm)],[c_970,c_1337]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_4,plain,
% 1.99/1.01      ( r2_hidden(X0,X1)
% 1.99/1.01      | ~ r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0),X1) ),
% 1.99/1.01      inference(cnf_transformation,[],[f77]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_978,plain,
% 1.99/1.01      ( r2_hidden(X0_47,X0_48)
% 1.99/1.01      | ~ r1_tarski(k6_enumset1(X1_47,X1_47,X1_47,X1_47,X1_47,X1_47,X1_47,X0_47),X0_48) ),
% 1.99/1.01      inference(subtyping,[status(esa)],[c_4]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_1225,plain,
% 1.99/1.01      ( r2_hidden(X0_47,X0_48) = iProver_top
% 1.99/1.01      | r1_tarski(k6_enumset1(X1_47,X1_47,X1_47,X1_47,X1_47,X1_47,X1_47,X0_47),X0_48) != iProver_top ),
% 1.99/1.01      inference(predicate_to_equality,[status(thm)],[c_978]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_1603,plain,
% 1.99/1.01      ( r2_hidden(sK1,X0_48) = iProver_top
% 1.99/1.01      | r1_tarski(k1_relat_1(sK3),X0_48) != iProver_top ),
% 1.99/1.01      inference(superposition,[status(thm)],[c_1393,c_1225]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_2228,plain,
% 1.99/1.01      ( r2_hidden(sK1,k1_relat_1(sK3)) = iProver_top ),
% 1.99/1.01      inference(superposition,[status(thm)],[c_1505,c_1603]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_2,plain,
% 1.99/1.01      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 1.99/1.01      inference(cnf_transformation,[],[f40]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_980,plain,
% 1.99/1.01      ( ~ r2_hidden(X0_47,X0_48)
% 1.99/1.01      | r2_hidden(X0_47,X1_48)
% 1.99/1.01      | ~ r1_tarski(X0_48,X1_48) ),
% 1.99/1.01      inference(subtyping,[status(esa)],[c_2]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_1424,plain,
% 1.99/1.01      ( ~ r2_hidden(k1_funct_1(sK3,sK1),X0_48)
% 1.99/1.01      | r2_hidden(k1_funct_1(sK3,sK1),sK2)
% 1.99/1.01      | ~ r1_tarski(X0_48,sK2) ),
% 1.99/1.01      inference(instantiation,[status(thm)],[c_980]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_1994,plain,
% 1.99/1.01      ( ~ r2_hidden(k1_funct_1(sK3,sK1),k2_relat_1(sK3))
% 1.99/1.01      | r2_hidden(k1_funct_1(sK3,sK1),sK2)
% 1.99/1.01      | ~ r1_tarski(k2_relat_1(sK3),sK2) ),
% 1.99/1.01      inference(instantiation,[status(thm)],[c_1424]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_1995,plain,
% 1.99/1.01      ( r2_hidden(k1_funct_1(sK3,sK1),k2_relat_1(sK3)) != iProver_top
% 1.99/1.01      | r2_hidden(k1_funct_1(sK3,sK1),sK2) = iProver_top
% 1.99/1.01      | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top ),
% 1.99/1.01      inference(predicate_to_equality,[status(thm)],[c_1994]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_9,plain,
% 1.99/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.99/1.01      | v1_relat_1(X0) ),
% 1.99/1.01      inference(cnf_transformation,[],[f56]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_8,plain,
% 1.99/1.01      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 1.99/1.01      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 1.99/1.01      | ~ v1_funct_1(X1)
% 1.99/1.01      | ~ v1_relat_1(X1) ),
% 1.99/1.01      inference(cnf_transformation,[],[f55]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_22,negated_conjecture,
% 1.99/1.01      ( v1_funct_1(sK3) ),
% 1.99/1.01      inference(cnf_transformation,[],[f65]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_251,plain,
% 1.99/1.01      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 1.99/1.01      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 1.99/1.01      | ~ v1_relat_1(X1)
% 1.99/1.01      | sK3 != X1 ),
% 1.99/1.01      inference(resolution_lifted,[status(thm)],[c_8,c_22]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_252,plain,
% 1.99/1.01      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 1.99/1.01      | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3))
% 1.99/1.01      | ~ v1_relat_1(sK3) ),
% 1.99/1.01      inference(unflattening,[status(thm)],[c_251]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_292,plain,
% 1.99/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.99/1.01      | ~ r2_hidden(X3,k1_relat_1(sK3))
% 1.99/1.01      | r2_hidden(k1_funct_1(sK3,X3),k2_relat_1(sK3))
% 1.99/1.01      | sK3 != X0 ),
% 1.99/1.01      inference(resolution_lifted,[status(thm)],[c_9,c_252]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_293,plain,
% 1.99/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.99/1.01      | ~ r2_hidden(X2,k1_relat_1(sK3))
% 1.99/1.01      | r2_hidden(k1_funct_1(sK3,X2),k2_relat_1(sK3)) ),
% 1.99/1.01      inference(unflattening,[status(thm)],[c_292]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_433,plain,
% 1.99/1.01      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 1.99/1.01      | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3))
% 1.99/1.01      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 1.99/1.01      | sK3 != sK3 ),
% 1.99/1.01      inference(resolution_lifted,[status(thm)],[c_20,c_293]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_735,plain,
% 1.99/1.01      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 1.99/1.01      | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3))
% 1.99/1.01      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
% 1.99/1.01      inference(equality_resolution_simp,[status(thm)],[c_433]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_969,plain,
% 1.99/1.01      ( ~ r2_hidden(X0_47,k1_relat_1(sK3))
% 1.99/1.01      | r2_hidden(k1_funct_1(sK3,X0_47),k2_relat_1(sK3))
% 1.99/1.01      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)) ),
% 1.99/1.01      inference(subtyping,[status(esa)],[c_735]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_983,plain,
% 1.99/1.01      ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))
% 1.99/1.01      | ~ sP0_iProver_split ),
% 1.99/1.01      inference(splitting,
% 1.99/1.01                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.99/1.01                [c_969]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_1231,plain,
% 1.99/1.01      ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))
% 1.99/1.01      | sP0_iProver_split != iProver_top ),
% 1.99/1.01      inference(predicate_to_equality,[status(thm)],[c_983]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_1870,plain,
% 1.99/1.01      ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))
% 1.99/1.01      | sP0_iProver_split != iProver_top ),
% 1.99/1.01      inference(light_normalisation,[status(thm)],[c_1231,c_1393]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_1876,plain,
% 1.99/1.01      ( sP0_iProver_split != iProver_top ),
% 1.99/1.01      inference(equality_resolution,[status(thm)],[c_1870]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_7,plain,
% 1.99/1.01      ( ~ v5_relat_1(X0,X1)
% 1.99/1.01      | r1_tarski(k2_relat_1(X0),X1)
% 1.99/1.01      | ~ v1_relat_1(X0) ),
% 1.99/1.01      inference(cnf_transformation,[],[f53]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_10,plain,
% 1.99/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.99/1.01      | v5_relat_1(X0,X2) ),
% 1.99/1.01      inference(cnf_transformation,[],[f57]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_271,plain,
% 1.99/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.99/1.01      | r1_tarski(k2_relat_1(X3),X4)
% 1.99/1.01      | ~ v1_relat_1(X3)
% 1.99/1.01      | X0 != X3
% 1.99/1.01      | X2 != X4 ),
% 1.99/1.01      inference(resolution_lifted,[status(thm)],[c_7,c_10]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_272,plain,
% 1.99/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.99/1.01      | r1_tarski(k2_relat_1(X0),X2)
% 1.99/1.01      | ~ v1_relat_1(X0) ),
% 1.99/1.01      inference(unflattening,[status(thm)],[c_271]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_276,plain,
% 1.99/1.01      ( r1_tarski(k2_relat_1(X0),X2)
% 1.99/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 1.99/1.01      inference(global_propositional_subsumption,
% 1.99/1.01                [status(thm)],
% 1.99/1.01                [c_272,c_9]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_277,plain,
% 1.99/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.99/1.01      | r1_tarski(k2_relat_1(X0),X2) ),
% 1.99/1.01      inference(renaming,[status(thm)],[c_276]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_311,plain,
% 1.99/1.01      ( r1_tarski(k2_relat_1(X0),X1)
% 1.99/1.01      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X1))
% 1.99/1.01      | sK3 != X0 ),
% 1.99/1.01      inference(resolution_lifted,[status(thm)],[c_277,c_20]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_312,plain,
% 1.99/1.01      ( r1_tarski(k2_relat_1(sK3),X0)
% 1.99/1.01      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X0)) ),
% 1.99/1.01      inference(unflattening,[status(thm)],[c_311]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_974,plain,
% 1.99/1.01      ( r1_tarski(k2_relat_1(sK3),X0_48)
% 1.99/1.01      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1_48,X0_48)) ),
% 1.99/1.01      inference(subtyping,[status(esa)],[c_312]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_1373,plain,
% 1.99/1.01      ( r1_tarski(k2_relat_1(sK3),sK2)
% 1.99/1.01      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) ),
% 1.99/1.01      inference(instantiation,[status(thm)],[c_974]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_1374,plain,
% 1.99/1.01      ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2))
% 1.99/1.01      | r1_tarski(k2_relat_1(sK3),sK2) = iProver_top ),
% 1.99/1.01      inference(predicate_to_equality,[status(thm)],[c_1373]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_989,plain,( X0_49 = X0_49 ),theory(equality) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_1329,plain,
% 1.99/1.01      ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) = k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) ),
% 1.99/1.01      inference(instantiation,[status(thm)],[c_989]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_984,plain,
% 1.99/1.01      ( ~ r2_hidden(X0_47,k1_relat_1(sK3))
% 1.99/1.01      | r2_hidden(k1_funct_1(sK3,X0_47),k2_relat_1(sK3))
% 1.99/1.01      | ~ sP1_iProver_split ),
% 1.99/1.01      inference(splitting,
% 1.99/1.01                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 1.99/1.01                [c_969]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_1032,plain,
% 1.99/1.01      ( r2_hidden(X0_47,k1_relat_1(sK3)) != iProver_top
% 1.99/1.01      | r2_hidden(k1_funct_1(sK3,X0_47),k2_relat_1(sK3)) = iProver_top
% 1.99/1.01      | sP1_iProver_split != iProver_top ),
% 1.99/1.01      inference(predicate_to_equality,[status(thm)],[c_984]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_1034,plain,
% 1.99/1.01      ( r2_hidden(k1_funct_1(sK3,sK1),k2_relat_1(sK3)) = iProver_top
% 1.99/1.01      | r2_hidden(sK1,k1_relat_1(sK3)) != iProver_top
% 1.99/1.01      | sP1_iProver_split != iProver_top ),
% 1.99/1.01      inference(instantiation,[status(thm)],[c_1032]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_985,plain,
% 1.99/1.01      ( sP1_iProver_split | sP0_iProver_split ),
% 1.99/1.01      inference(splitting,
% 1.99/1.01                [splitting(split),new_symbols(definition,[])],
% 1.99/1.01                [c_969]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_1031,plain,
% 1.99/1.01      ( sP1_iProver_split = iProver_top
% 1.99/1.01      | sP0_iProver_split = iProver_top ),
% 1.99/1.01      inference(predicate_to_equality,[status(thm)],[c_985]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_18,negated_conjecture,
% 1.99/1.01      ( ~ r2_hidden(k1_funct_1(sK3,sK1),sK2) ),
% 1.99/1.01      inference(cnf_transformation,[],[f69]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_26,plain,
% 1.99/1.01      ( r2_hidden(k1_funct_1(sK3,sK1),sK2) != iProver_top ),
% 1.99/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(contradiction,plain,
% 1.99/1.01      ( $false ),
% 1.99/1.01      inference(minisat,
% 1.99/1.01                [status(thm)],
% 1.99/1.01                [c_2228,c_1995,c_1876,c_1374,c_1329,c_1034,c_1031,c_26]) ).
% 1.99/1.01  
% 1.99/1.01  
% 1.99/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 1.99/1.01  
% 1.99/1.01  ------                               Statistics
% 1.99/1.01  
% 1.99/1.01  ------ General
% 1.99/1.01  
% 1.99/1.01  abstr_ref_over_cycles:                  0
% 1.99/1.01  abstr_ref_under_cycles:                 0
% 1.99/1.01  gc_basic_clause_elim:                   0
% 1.99/1.01  forced_gc_time:                         0
% 1.99/1.01  parsing_time:                           0.011
% 1.99/1.01  unif_index_cands_time:                  0.
% 1.99/1.01  unif_index_add_time:                    0.
% 1.99/1.01  orderings_time:                         0.
% 1.99/1.01  out_proof_time:                         0.017
% 1.99/1.01  total_time:                             0.112
% 1.99/1.01  num_of_symbols:                         53
% 1.99/1.01  num_of_terms:                           2250
% 1.99/1.01  
% 1.99/1.01  ------ Preprocessing
% 1.99/1.01  
% 1.99/1.01  num_of_splits:                          2
% 1.99/1.01  num_of_split_atoms:                     2
% 1.99/1.01  num_of_reused_defs:                     0
% 1.99/1.01  num_eq_ax_congr_red:                    16
% 1.99/1.01  num_of_sem_filtered_clauses:            1
% 1.99/1.01  num_of_subtypes:                        4
% 1.99/1.01  monotx_restored_types:                  0
% 1.99/1.01  sat_num_of_epr_types:                   0
% 1.99/1.01  sat_num_of_non_cyclic_types:            0
% 1.99/1.01  sat_guarded_non_collapsed_types:        0
% 1.99/1.01  num_pure_diseq_elim:                    0
% 1.99/1.01  simp_replaced_by:                       0
% 1.99/1.01  res_preprocessed:                       100
% 1.99/1.01  prep_upred:                             0
% 1.99/1.01  prep_unflattend:                        66
% 1.99/1.01  smt_new_axioms:                         0
% 1.99/1.01  pred_elim_cands:                        2
% 1.99/1.01  pred_elim:                              5
% 1.99/1.01  pred_elim_cl:                           9
% 1.99/1.01  pred_elim_cycles:                       8
% 1.99/1.01  merged_defs:                            0
% 1.99/1.01  merged_defs_ncl:                        0
% 1.99/1.01  bin_hyper_res:                          0
% 1.99/1.01  prep_cycles:                            4
% 1.99/1.01  pred_elim_time:                         0.013
% 1.99/1.01  splitting_time:                         0.
% 1.99/1.01  sem_filter_time:                        0.
% 1.99/1.01  monotx_time:                            0.
% 1.99/1.01  subtype_inf_time:                       0.
% 1.99/1.01  
% 1.99/1.01  ------ Problem properties
% 1.99/1.01  
% 1.99/1.01  clauses:                                16
% 1.99/1.01  conjectures:                            2
% 1.99/1.01  epr:                                    3
% 1.99/1.01  horn:                                   13
% 1.99/1.01  ground:                                 6
% 1.99/1.01  unary:                                  3
% 1.99/1.01  binary:                                 8
% 1.99/1.01  lits:                                   35
% 1.99/1.01  lits_eq:                                13
% 1.99/1.01  fd_pure:                                0
% 1.99/1.01  fd_pseudo:                              0
% 1.99/1.01  fd_cond:                                0
% 1.99/1.01  fd_pseudo_cond:                         0
% 1.99/1.01  ac_symbols:                             0
% 1.99/1.01  
% 1.99/1.01  ------ Propositional Solver
% 1.99/1.01  
% 1.99/1.01  prop_solver_calls:                      27
% 1.99/1.01  prop_fast_solver_calls:                 652
% 1.99/1.01  smt_solver_calls:                       0
% 1.99/1.01  smt_fast_solver_calls:                  0
% 1.99/1.01  prop_num_of_clauses:                    701
% 1.99/1.01  prop_preprocess_simplified:             3116
% 1.99/1.01  prop_fo_subsumed:                       6
% 1.99/1.01  prop_solver_time:                       0.
% 1.99/1.01  smt_solver_time:                        0.
% 1.99/1.01  smt_fast_solver_time:                   0.
% 1.99/1.01  prop_fast_solver_time:                  0.
% 1.99/1.01  prop_unsat_core_time:                   0.
% 1.99/1.01  
% 1.99/1.01  ------ QBF
% 1.99/1.01  
% 1.99/1.01  qbf_q_res:                              0
% 1.99/1.01  qbf_num_tautologies:                    0
% 1.99/1.01  qbf_prep_cycles:                        0
% 1.99/1.01  
% 1.99/1.01  ------ BMC1
% 1.99/1.01  
% 1.99/1.01  bmc1_current_bound:                     -1
% 1.99/1.01  bmc1_last_solved_bound:                 -1
% 1.99/1.01  bmc1_unsat_core_size:                   -1
% 1.99/1.01  bmc1_unsat_core_parents_size:           -1
% 1.99/1.01  bmc1_merge_next_fun:                    0
% 1.99/1.01  bmc1_unsat_core_clauses_time:           0.
% 1.99/1.01  
% 1.99/1.01  ------ Instantiation
% 1.99/1.01  
% 1.99/1.01  inst_num_of_clauses:                    177
% 1.99/1.01  inst_num_in_passive:                    40
% 1.99/1.01  inst_num_in_active:                     100
% 1.99/1.01  inst_num_in_unprocessed:                37
% 1.99/1.01  inst_num_of_loops:                      120
% 1.99/1.01  inst_num_of_learning_restarts:          0
% 1.99/1.01  inst_num_moves_active_passive:          17
% 1.99/1.01  inst_lit_activity:                      0
% 1.99/1.01  inst_lit_activity_moves:                0
% 1.99/1.01  inst_num_tautologies:                   0
% 1.99/1.01  inst_num_prop_implied:                  0
% 1.99/1.01  inst_num_existing_simplified:           0
% 1.99/1.01  inst_num_eq_res_simplified:             0
% 1.99/1.01  inst_num_child_elim:                    0
% 1.99/1.01  inst_num_of_dismatching_blockings:      42
% 1.99/1.01  inst_num_of_non_proper_insts:           157
% 1.99/1.01  inst_num_of_duplicates:                 0
% 1.99/1.01  inst_inst_num_from_inst_to_res:         0
% 1.99/1.01  inst_dismatching_checking_time:         0.
% 1.99/1.01  
% 1.99/1.01  ------ Resolution
% 1.99/1.01  
% 1.99/1.01  res_num_of_clauses:                     0
% 1.99/1.01  res_num_in_passive:                     0
% 1.99/1.01  res_num_in_active:                      0
% 1.99/1.01  res_num_of_loops:                       104
% 1.99/1.01  res_forward_subset_subsumed:            26
% 1.99/1.01  res_backward_subset_subsumed:           0
% 1.99/1.01  res_forward_subsumed:                   0
% 1.99/1.01  res_backward_subsumed:                  0
% 1.99/1.01  res_forward_subsumption_resolution:     0
% 1.99/1.01  res_backward_subsumption_resolution:    0
% 1.99/1.01  res_clause_to_clause_subsumption:       67
% 1.99/1.01  res_orphan_elimination:                 0
% 1.99/1.01  res_tautology_del:                      14
% 1.99/1.01  res_num_eq_res_simplified:              2
% 1.99/1.01  res_num_sel_changes:                    0
% 1.99/1.01  res_moves_from_active_to_pass:          0
% 1.99/1.01  
% 1.99/1.01  ------ Superposition
% 1.99/1.01  
% 1.99/1.01  sup_time_total:                         0.
% 1.99/1.01  sup_time_generating:                    0.
% 1.99/1.01  sup_time_sim_full:                      0.
% 1.99/1.01  sup_time_sim_immed:                     0.
% 1.99/1.01  
% 1.99/1.01  sup_num_of_clauses:                     27
% 1.99/1.01  sup_num_in_active:                      20
% 1.99/1.01  sup_num_in_passive:                     7
% 1.99/1.01  sup_num_of_loops:                       22
% 1.99/1.01  sup_fw_superposition:                   3
% 1.99/1.01  sup_bw_superposition:                   9
% 1.99/1.01  sup_immediate_simplified:               0
% 1.99/1.01  sup_given_eliminated:                   0
% 1.99/1.01  comparisons_done:                       0
% 1.99/1.01  comparisons_avoided:                    0
% 1.99/1.01  
% 1.99/1.01  ------ Simplifications
% 1.99/1.01  
% 1.99/1.01  
% 1.99/1.01  sim_fw_subset_subsumed:                 0
% 1.99/1.01  sim_bw_subset_subsumed:                 0
% 1.99/1.01  sim_fw_subsumed:                        0
% 1.99/1.01  sim_bw_subsumed:                        0
% 1.99/1.01  sim_fw_subsumption_res:                 0
% 1.99/1.01  sim_bw_subsumption_res:                 0
% 1.99/1.01  sim_tautology_del:                      3
% 1.99/1.01  sim_eq_tautology_del:                   0
% 1.99/1.01  sim_eq_res_simp:                        0
% 1.99/1.01  sim_fw_demodulated:                     0
% 1.99/1.01  sim_bw_demodulated:                     3
% 1.99/1.01  sim_light_normalised:                   3
% 1.99/1.01  sim_joinable_taut:                      0
% 1.99/1.01  sim_joinable_simp:                      0
% 1.99/1.01  sim_ac_normalised:                      0
% 1.99/1.01  sim_smt_subsumption:                    0
% 1.99/1.01  
%------------------------------------------------------------------------------
