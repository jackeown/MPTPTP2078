%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:06:07 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 694 expanded)
%              Number of clauses        :   57 ( 113 expanded)
%              Number of leaves         :   19 ( 184 expanded)
%              Depth                    :   24
%              Number of atoms          :  365 (1662 expanded)
%              Number of equality atoms :  182 ( 787 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f38,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f39,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f38])).

fof(f54,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(X3,X2) != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
   => ( k1_funct_1(sK6,sK5) != sK4
      & r2_hidden(sK5,sK3)
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4))))
      & v1_funct_2(sK6,sK3,k1_tarski(sK4))
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( k1_funct_1(sK6,sK5) != sK4
    & r2_hidden(sK5,sK3)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4))))
    & v1_funct_2(sK6,sK3,k1_tarski(sK4))
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f39,f54])).

fof(f98,plain,(
    r2_hidden(sK5,sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f96,plain,(
    v1_funct_2(sK6,sK3,k1_tarski(sK4)) ),
    inference(cnf_transformation,[],[f55])).

fof(f8,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f14])).

fof(f100,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f79,f80])).

fof(f101,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f78,f100])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f77,f101])).

fof(f103,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f76,f102])).

fof(f104,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f75,f103])).

fof(f105,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f74,f104])).

fof(f120,plain,(
    v1_funct_2(sK6,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(definition_unfolding,[],[f96,f105])).

fof(f22,axiom,(
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

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f97,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4)))) ),
    inference(cnf_transformation,[],[f55])).

fof(f119,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) ),
    inference(definition_unfolding,[],[f97,f105])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f81,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f118,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f81,f105,f105,f105])).

fof(f127,plain,(
    ! [X1] : k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(equality_resolution,[],[f118])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f95,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f55])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k2_relat_1(X1))
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,k2_relat_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,k2_relat_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,k2_relat_1(X1))
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK1(X0,X1) != X0
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( sK1(X0,X1) = X0
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK1(X0,X1) != X0
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( sK1(X0,X1) = X0
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f47,f48])).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f116,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f70,f105])).

fof(f126,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f116])).

fof(f99,plain,(
    k1_funct_1(sK6,sK5) != sK4 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_32,negated_conjecture,
    ( r2_hidden(sK5,sK3) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1122,plain,
    ( r2_hidden(sK5,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK6,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_424,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK6 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_33])).

cnf(c_425,plain,
    ( ~ v1_funct_2(sK6,X0,X1)
    | k1_relset_1(X0,X1,sK6) = X0
    | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_424])).

cnf(c_598,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != X0
    | k1_relset_1(X1,X0,sK6) = X1
    | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0))
    | sK3 != X1
    | sK6 != sK6
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_425])).

cnf(c_599,plain,
    ( k1_relset_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK6) = sK3
    | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))
    | k1_xboole_0 = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(unflattening,[status(thm)],[c_598])).

cnf(c_670,plain,
    ( k1_relset_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK6) = sK3
    | k1_xboole_0 = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(equality_resolution_simp,[status(thm)],[c_599])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_460,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_33])).

cnf(c_461,plain,
    ( k1_relset_1(X0,X1,sK6) = k1_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_460])).

cnf(c_1326,plain,
    ( k1_relset_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK6) = k1_relat_1(sK6) ),
    inference(equality_resolution,[status(thm)],[c_461])).

cnf(c_1426,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k1_xboole_0
    | k1_relat_1(sK6) = sK3 ),
    inference(demodulation,[status(thm)],[c_670,c_1326])).

cnf(c_1433,plain,
    ( k1_relset_1(X0,X1,sK6) = k1_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))
    | k1_relat_1(sK6) = sK3 ),
    inference(superposition,[status(thm)],[c_1426,c_461])).

cnf(c_18,plain,
    ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_1764,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | k1_relat_1(sK6) = sK3 ),
    inference(superposition,[status(thm)],[c_1426,c_18])).

cnf(c_11,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1766,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k1_xboole_0
    | k1_relat_1(sK6) = sK3 ),
    inference(demodulation,[status(thm)],[c_1764,c_11])).

cnf(c_1767,plain,
    ( k1_relat_1(sK6) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1433,c_1426,c_1766])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_346,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_35])).

cnf(c_347,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK6))
    | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6))
    | ~ v1_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_346])).

cnf(c_390,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(sK6))
    | r2_hidden(k1_funct_1(sK6,X3),k2_relat_1(sK6))
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_347])).

cnf(c_391,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r2_hidden(X2,k1_relat_1(sK6))
    | r2_hidden(k1_funct_1(sK6,X2),k2_relat_1(sK6)) ),
    inference(unflattening,[status(thm)],[c_390])).

cnf(c_534,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK6))
    | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6))
    | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK6 != sK6 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_391])).

cnf(c_671,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK6))
    | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6))
    | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
    inference(equality_resolution_simp,[status(thm)],[c_534])).

cnf(c_782,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK6))
    | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_671])).

cnf(c_1119,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_782])).

cnf(c_1770,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_1767,c_1119])).

cnf(c_19,plain,
    ( ~ v5_relat_1(X0,X1)
    | r2_hidden(X2,X1)
    | ~ r2_hidden(X2,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v5_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_365,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(X3,X4)
    | ~ r2_hidden(X3,k2_relat_1(X5))
    | ~ v1_relat_1(X5)
    | X0 != X5
    | X2 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_22])).

cnf(c_366,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(X3,X2)
    | ~ r2_hidden(X3,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_365])).

cnf(c_370,plain,
    ( ~ r2_hidden(X3,k2_relat_1(X0))
    | r2_hidden(X3,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_366,c_21])).

cnf(c_371,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(X3,X2)
    | ~ r2_hidden(X3,k2_relat_1(X0)) ),
    inference(renaming,[status(thm)],[c_370])).

cnf(c_409,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k2_relat_1(X2))
    | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X3,X1))
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_371,c_33])).

cnf(c_410,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k2_relat_1(sK6))
    | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X2,X1)) ),
    inference(unflattening,[status(thm)],[c_409])).

cnf(c_1121,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | r2_hidden(X2,X1) = iProver_top
    | r2_hidden(X2,k2_relat_1(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_410])).

cnf(c_1422,plain,
    ( r2_hidden(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1121])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f126])).

cnf(c_1124,plain,
    ( X0 = X1
    | r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3231,plain,
    ( sK4 = X0
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1422,c_1124])).

cnf(c_3779,plain,
    ( k1_funct_1(sK6,X0) = sK4
    | r2_hidden(X0,sK3) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1770,c_3231])).

cnf(c_783,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_671])).

cnf(c_809,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_783])).

cnf(c_781,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_671])).

cnf(c_1120,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_781])).

cnf(c_2304,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1120])).

cnf(c_3794,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | k1_funct_1(sK6,X0) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3779,c_809,c_2304])).

cnf(c_3795,plain,
    ( k1_funct_1(sK6,X0) = sK4
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_3794])).

cnf(c_3803,plain,
    ( k1_funct_1(sK6,sK5) = sK4 ),
    inference(superposition,[status(thm)],[c_1122,c_3795])).

cnf(c_31,negated_conjecture,
    ( k1_funct_1(sK6,sK5) != sK4 ),
    inference(cnf_transformation,[],[f99])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3803,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:02:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.06/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.06/1.00  
% 3.06/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.06/1.00  
% 3.06/1.00  ------  iProver source info
% 3.06/1.00  
% 3.06/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.06/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.06/1.00  git: non_committed_changes: false
% 3.06/1.00  git: last_make_outside_of_git: false
% 3.06/1.00  
% 3.06/1.00  ------ 
% 3.06/1.00  
% 3.06/1.00  ------ Input Options
% 3.06/1.00  
% 3.06/1.00  --out_options                           all
% 3.06/1.00  --tptp_safe_out                         true
% 3.06/1.00  --problem_path                          ""
% 3.06/1.00  --include_path                          ""
% 3.06/1.00  --clausifier                            res/vclausify_rel
% 3.06/1.00  --clausifier_options                    --mode clausify
% 3.06/1.00  --stdin                                 false
% 3.06/1.00  --stats_out                             all
% 3.06/1.00  
% 3.06/1.00  ------ General Options
% 3.06/1.00  
% 3.06/1.00  --fof                                   false
% 3.06/1.00  --time_out_real                         305.
% 3.06/1.00  --time_out_virtual                      -1.
% 3.06/1.00  --symbol_type_check                     false
% 3.06/1.00  --clausify_out                          false
% 3.06/1.00  --sig_cnt_out                           false
% 3.06/1.00  --trig_cnt_out                          false
% 3.06/1.00  --trig_cnt_out_tolerance                1.
% 3.06/1.00  --trig_cnt_out_sk_spl                   false
% 3.06/1.00  --abstr_cl_out                          false
% 3.06/1.00  
% 3.06/1.00  ------ Global Options
% 3.06/1.00  
% 3.06/1.00  --schedule                              default
% 3.06/1.00  --add_important_lit                     false
% 3.06/1.00  --prop_solver_per_cl                    1000
% 3.06/1.00  --min_unsat_core                        false
% 3.06/1.00  --soft_assumptions                      false
% 3.06/1.00  --soft_lemma_size                       3
% 3.06/1.00  --prop_impl_unit_size                   0
% 3.06/1.00  --prop_impl_unit                        []
% 3.06/1.00  --share_sel_clauses                     true
% 3.06/1.00  --reset_solvers                         false
% 3.06/1.00  --bc_imp_inh                            [conj_cone]
% 3.06/1.00  --conj_cone_tolerance                   3.
% 3.06/1.00  --extra_neg_conj                        none
% 3.06/1.00  --large_theory_mode                     true
% 3.06/1.00  --prolific_symb_bound                   200
% 3.06/1.00  --lt_threshold                          2000
% 3.06/1.00  --clause_weak_htbl                      true
% 3.06/1.00  --gc_record_bc_elim                     false
% 3.06/1.00  
% 3.06/1.00  ------ Preprocessing Options
% 3.06/1.00  
% 3.06/1.00  --preprocessing_flag                    true
% 3.06/1.00  --time_out_prep_mult                    0.1
% 3.06/1.00  --splitting_mode                        input
% 3.06/1.00  --splitting_grd                         true
% 3.06/1.00  --splitting_cvd                         false
% 3.06/1.00  --splitting_cvd_svl                     false
% 3.06/1.00  --splitting_nvd                         32
% 3.06/1.00  --sub_typing                            true
% 3.06/1.00  --prep_gs_sim                           true
% 3.06/1.00  --prep_unflatten                        true
% 3.06/1.00  --prep_res_sim                          true
% 3.06/1.00  --prep_upred                            true
% 3.06/1.00  --prep_sem_filter                       exhaustive
% 3.06/1.00  --prep_sem_filter_out                   false
% 3.06/1.00  --pred_elim                             true
% 3.06/1.00  --res_sim_input                         true
% 3.06/1.00  --eq_ax_congr_red                       true
% 3.06/1.00  --pure_diseq_elim                       true
% 3.06/1.00  --brand_transform                       false
% 3.06/1.00  --non_eq_to_eq                          false
% 3.06/1.00  --prep_def_merge                        true
% 3.06/1.00  --prep_def_merge_prop_impl              false
% 3.06/1.00  --prep_def_merge_mbd                    true
% 3.06/1.00  --prep_def_merge_tr_red                 false
% 3.06/1.00  --prep_def_merge_tr_cl                  false
% 3.06/1.00  --smt_preprocessing                     true
% 3.06/1.00  --smt_ac_axioms                         fast
% 3.06/1.00  --preprocessed_out                      false
% 3.06/1.00  --preprocessed_stats                    false
% 3.06/1.00  
% 3.06/1.00  ------ Abstraction refinement Options
% 3.06/1.00  
% 3.06/1.00  --abstr_ref                             []
% 3.06/1.00  --abstr_ref_prep                        false
% 3.06/1.00  --abstr_ref_until_sat                   false
% 3.06/1.00  --abstr_ref_sig_restrict                funpre
% 3.06/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.06/1.00  --abstr_ref_under                       []
% 3.06/1.00  
% 3.06/1.00  ------ SAT Options
% 3.06/1.00  
% 3.06/1.00  --sat_mode                              false
% 3.06/1.00  --sat_fm_restart_options                ""
% 3.06/1.00  --sat_gr_def                            false
% 3.06/1.00  --sat_epr_types                         true
% 3.06/1.00  --sat_non_cyclic_types                  false
% 3.06/1.00  --sat_finite_models                     false
% 3.06/1.00  --sat_fm_lemmas                         false
% 3.06/1.00  --sat_fm_prep                           false
% 3.06/1.00  --sat_fm_uc_incr                        true
% 3.06/1.00  --sat_out_model                         small
% 3.06/1.00  --sat_out_clauses                       false
% 3.06/1.00  
% 3.06/1.00  ------ QBF Options
% 3.06/1.00  
% 3.06/1.00  --qbf_mode                              false
% 3.06/1.00  --qbf_elim_univ                         false
% 3.06/1.00  --qbf_dom_inst                          none
% 3.06/1.00  --qbf_dom_pre_inst                      false
% 3.06/1.00  --qbf_sk_in                             false
% 3.06/1.00  --qbf_pred_elim                         true
% 3.06/1.00  --qbf_split                             512
% 3.06/1.00  
% 3.06/1.00  ------ BMC1 Options
% 3.06/1.00  
% 3.06/1.00  --bmc1_incremental                      false
% 3.06/1.00  --bmc1_axioms                           reachable_all
% 3.06/1.00  --bmc1_min_bound                        0
% 3.06/1.00  --bmc1_max_bound                        -1
% 3.06/1.00  --bmc1_max_bound_default                -1
% 3.06/1.00  --bmc1_symbol_reachability              true
% 3.06/1.00  --bmc1_property_lemmas                  false
% 3.06/1.00  --bmc1_k_induction                      false
% 3.06/1.00  --bmc1_non_equiv_states                 false
% 3.06/1.00  --bmc1_deadlock                         false
% 3.06/1.00  --bmc1_ucm                              false
% 3.06/1.00  --bmc1_add_unsat_core                   none
% 3.06/1.00  --bmc1_unsat_core_children              false
% 3.06/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.06/1.00  --bmc1_out_stat                         full
% 3.06/1.00  --bmc1_ground_init                      false
% 3.06/1.00  --bmc1_pre_inst_next_state              false
% 3.06/1.00  --bmc1_pre_inst_state                   false
% 3.06/1.00  --bmc1_pre_inst_reach_state             false
% 3.06/1.00  --bmc1_out_unsat_core                   false
% 3.06/1.00  --bmc1_aig_witness_out                  false
% 3.06/1.00  --bmc1_verbose                          false
% 3.06/1.00  --bmc1_dump_clauses_tptp                false
% 3.06/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.06/1.00  --bmc1_dump_file                        -
% 3.06/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.06/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.06/1.00  --bmc1_ucm_extend_mode                  1
% 3.06/1.00  --bmc1_ucm_init_mode                    2
% 3.06/1.00  --bmc1_ucm_cone_mode                    none
% 3.06/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.06/1.00  --bmc1_ucm_relax_model                  4
% 3.06/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.06/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.06/1.00  --bmc1_ucm_layered_model                none
% 3.06/1.00  --bmc1_ucm_max_lemma_size               10
% 3.06/1.00  
% 3.06/1.00  ------ AIG Options
% 3.06/1.00  
% 3.06/1.00  --aig_mode                              false
% 3.06/1.00  
% 3.06/1.00  ------ Instantiation Options
% 3.06/1.00  
% 3.06/1.00  --instantiation_flag                    true
% 3.06/1.00  --inst_sos_flag                         false
% 3.06/1.00  --inst_sos_phase                        true
% 3.06/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.06/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.06/1.00  --inst_lit_sel_side                     num_symb
% 3.06/1.00  --inst_solver_per_active                1400
% 3.06/1.00  --inst_solver_calls_frac                1.
% 3.06/1.00  --inst_passive_queue_type               priority_queues
% 3.06/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.06/1.00  --inst_passive_queues_freq              [25;2]
% 3.06/1.00  --inst_dismatching                      true
% 3.06/1.00  --inst_eager_unprocessed_to_passive     true
% 3.06/1.00  --inst_prop_sim_given                   true
% 3.06/1.00  --inst_prop_sim_new                     false
% 3.06/1.00  --inst_subs_new                         false
% 3.06/1.00  --inst_eq_res_simp                      false
% 3.06/1.00  --inst_subs_given                       false
% 3.06/1.00  --inst_orphan_elimination               true
% 3.06/1.00  --inst_learning_loop_flag               true
% 3.06/1.00  --inst_learning_start                   3000
% 3.06/1.00  --inst_learning_factor                  2
% 3.06/1.00  --inst_start_prop_sim_after_learn       3
% 3.06/1.00  --inst_sel_renew                        solver
% 3.06/1.00  --inst_lit_activity_flag                true
% 3.06/1.00  --inst_restr_to_given                   false
% 3.06/1.00  --inst_activity_threshold               500
% 3.06/1.00  --inst_out_proof                        true
% 3.06/1.00  
% 3.06/1.00  ------ Resolution Options
% 3.06/1.00  
% 3.06/1.00  --resolution_flag                       true
% 3.06/1.00  --res_lit_sel                           adaptive
% 3.06/1.00  --res_lit_sel_side                      none
% 3.06/1.00  --res_ordering                          kbo
% 3.06/1.00  --res_to_prop_solver                    active
% 3.06/1.00  --res_prop_simpl_new                    false
% 3.06/1.00  --res_prop_simpl_given                  true
% 3.06/1.00  --res_passive_queue_type                priority_queues
% 3.06/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.06/1.00  --res_passive_queues_freq               [15;5]
% 3.06/1.00  --res_forward_subs                      full
% 3.06/1.00  --res_backward_subs                     full
% 3.06/1.00  --res_forward_subs_resolution           true
% 3.06/1.00  --res_backward_subs_resolution          true
% 3.06/1.00  --res_orphan_elimination                true
% 3.06/1.00  --res_time_limit                        2.
% 3.06/1.00  --res_out_proof                         true
% 3.06/1.00  
% 3.06/1.00  ------ Superposition Options
% 3.06/1.00  
% 3.06/1.00  --superposition_flag                    true
% 3.06/1.00  --sup_passive_queue_type                priority_queues
% 3.06/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.06/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.06/1.00  --demod_completeness_check              fast
% 3.06/1.00  --demod_use_ground                      true
% 3.06/1.00  --sup_to_prop_solver                    passive
% 3.06/1.00  --sup_prop_simpl_new                    true
% 3.06/1.00  --sup_prop_simpl_given                  true
% 3.06/1.00  --sup_fun_splitting                     false
% 3.06/1.00  --sup_smt_interval                      50000
% 3.06/1.00  
% 3.06/1.00  ------ Superposition Simplification Setup
% 3.06/1.00  
% 3.06/1.00  --sup_indices_passive                   []
% 3.06/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.06/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/1.00  --sup_full_bw                           [BwDemod]
% 3.06/1.00  --sup_immed_triv                        [TrivRules]
% 3.06/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.06/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/1.00  --sup_immed_bw_main                     []
% 3.06/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.06/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.06/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.06/1.00  
% 3.06/1.00  ------ Combination Options
% 3.06/1.00  
% 3.06/1.00  --comb_res_mult                         3
% 3.06/1.00  --comb_sup_mult                         2
% 3.06/1.00  --comb_inst_mult                        10
% 3.06/1.00  
% 3.06/1.00  ------ Debug Options
% 3.06/1.00  
% 3.06/1.00  --dbg_backtrace                         false
% 3.06/1.00  --dbg_dump_prop_clauses                 false
% 3.06/1.00  --dbg_dump_prop_clauses_file            -
% 3.06/1.00  --dbg_out_stat                          false
% 3.06/1.00  ------ Parsing...
% 3.06/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.06/1.00  
% 3.06/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.06/1.00  
% 3.06/1.00  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.06/1.00  
% 3.06/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.06/1.00  ------ Proving...
% 3.06/1.00  ------ Problem Properties 
% 3.06/1.00  
% 3.06/1.00  
% 3.06/1.00  clauses                                 30
% 3.06/1.00  conjectures                             2
% 3.06/1.00  EPR                                     2
% 3.06/1.00  Horn                                    19
% 3.06/1.00  unary                                   7
% 3.06/1.00  binary                                  9
% 3.06/1.00  lits                                    69
% 3.06/1.00  lits eq                                 29
% 3.06/1.00  fd_pure                                 0
% 3.06/1.00  fd_pseudo                               0
% 3.06/1.00  fd_cond                                 1
% 3.06/1.00  fd_pseudo_cond                          6
% 3.06/1.00  AC symbols                              0
% 3.06/1.00  
% 3.06/1.00  ------ Schedule dynamic 5 is on 
% 3.06/1.00  
% 3.06/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.06/1.00  
% 3.06/1.00  
% 3.06/1.00  ------ 
% 3.06/1.00  Current options:
% 3.06/1.00  ------ 
% 3.06/1.00  
% 3.06/1.00  ------ Input Options
% 3.06/1.00  
% 3.06/1.00  --out_options                           all
% 3.06/1.00  --tptp_safe_out                         true
% 3.06/1.00  --problem_path                          ""
% 3.06/1.00  --include_path                          ""
% 3.06/1.00  --clausifier                            res/vclausify_rel
% 3.06/1.00  --clausifier_options                    --mode clausify
% 3.06/1.00  --stdin                                 false
% 3.06/1.00  --stats_out                             all
% 3.06/1.00  
% 3.06/1.00  ------ General Options
% 3.06/1.00  
% 3.06/1.00  --fof                                   false
% 3.06/1.00  --time_out_real                         305.
% 3.06/1.00  --time_out_virtual                      -1.
% 3.06/1.00  --symbol_type_check                     false
% 3.06/1.00  --clausify_out                          false
% 3.06/1.00  --sig_cnt_out                           false
% 3.06/1.00  --trig_cnt_out                          false
% 3.06/1.00  --trig_cnt_out_tolerance                1.
% 3.06/1.00  --trig_cnt_out_sk_spl                   false
% 3.06/1.00  --abstr_cl_out                          false
% 3.06/1.00  
% 3.06/1.00  ------ Global Options
% 3.06/1.00  
% 3.06/1.00  --schedule                              default
% 3.06/1.00  --add_important_lit                     false
% 3.06/1.00  --prop_solver_per_cl                    1000
% 3.06/1.00  --min_unsat_core                        false
% 3.06/1.00  --soft_assumptions                      false
% 3.06/1.00  --soft_lemma_size                       3
% 3.06/1.00  --prop_impl_unit_size                   0
% 3.06/1.00  --prop_impl_unit                        []
% 3.06/1.00  --share_sel_clauses                     true
% 3.06/1.00  --reset_solvers                         false
% 3.06/1.00  --bc_imp_inh                            [conj_cone]
% 3.06/1.00  --conj_cone_tolerance                   3.
% 3.06/1.00  --extra_neg_conj                        none
% 3.06/1.00  --large_theory_mode                     true
% 3.06/1.00  --prolific_symb_bound                   200
% 3.06/1.00  --lt_threshold                          2000
% 3.06/1.00  --clause_weak_htbl                      true
% 3.06/1.00  --gc_record_bc_elim                     false
% 3.06/1.00  
% 3.06/1.00  ------ Preprocessing Options
% 3.06/1.00  
% 3.06/1.00  --preprocessing_flag                    true
% 3.06/1.00  --time_out_prep_mult                    0.1
% 3.06/1.00  --splitting_mode                        input
% 3.06/1.00  --splitting_grd                         true
% 3.06/1.00  --splitting_cvd                         false
% 3.06/1.00  --splitting_cvd_svl                     false
% 3.06/1.00  --splitting_nvd                         32
% 3.06/1.00  --sub_typing                            true
% 3.06/1.00  --prep_gs_sim                           true
% 3.06/1.00  --prep_unflatten                        true
% 3.06/1.00  --prep_res_sim                          true
% 3.06/1.00  --prep_upred                            true
% 3.06/1.00  --prep_sem_filter                       exhaustive
% 3.06/1.00  --prep_sem_filter_out                   false
% 3.06/1.00  --pred_elim                             true
% 3.06/1.00  --res_sim_input                         true
% 3.06/1.00  --eq_ax_congr_red                       true
% 3.06/1.00  --pure_diseq_elim                       true
% 3.06/1.00  --brand_transform                       false
% 3.06/1.00  --non_eq_to_eq                          false
% 3.06/1.00  --prep_def_merge                        true
% 3.06/1.00  --prep_def_merge_prop_impl              false
% 3.06/1.00  --prep_def_merge_mbd                    true
% 3.06/1.00  --prep_def_merge_tr_red                 false
% 3.06/1.00  --prep_def_merge_tr_cl                  false
% 3.06/1.00  --smt_preprocessing                     true
% 3.06/1.00  --smt_ac_axioms                         fast
% 3.06/1.00  --preprocessed_out                      false
% 3.06/1.00  --preprocessed_stats                    false
% 3.06/1.00  
% 3.06/1.00  ------ Abstraction refinement Options
% 3.06/1.00  
% 3.06/1.00  --abstr_ref                             []
% 3.06/1.00  --abstr_ref_prep                        false
% 3.06/1.00  --abstr_ref_until_sat                   false
% 3.06/1.00  --abstr_ref_sig_restrict                funpre
% 3.06/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.06/1.00  --abstr_ref_under                       []
% 3.06/1.00  
% 3.06/1.00  ------ SAT Options
% 3.06/1.00  
% 3.06/1.00  --sat_mode                              false
% 3.06/1.00  --sat_fm_restart_options                ""
% 3.06/1.00  --sat_gr_def                            false
% 3.06/1.00  --sat_epr_types                         true
% 3.06/1.00  --sat_non_cyclic_types                  false
% 3.06/1.00  --sat_finite_models                     false
% 3.06/1.00  --sat_fm_lemmas                         false
% 3.06/1.00  --sat_fm_prep                           false
% 3.06/1.00  --sat_fm_uc_incr                        true
% 3.06/1.00  --sat_out_model                         small
% 3.06/1.00  --sat_out_clauses                       false
% 3.06/1.00  
% 3.06/1.00  ------ QBF Options
% 3.06/1.00  
% 3.06/1.00  --qbf_mode                              false
% 3.06/1.00  --qbf_elim_univ                         false
% 3.06/1.00  --qbf_dom_inst                          none
% 3.06/1.00  --qbf_dom_pre_inst                      false
% 3.06/1.00  --qbf_sk_in                             false
% 3.06/1.00  --qbf_pred_elim                         true
% 3.06/1.00  --qbf_split                             512
% 3.06/1.00  
% 3.06/1.00  ------ BMC1 Options
% 3.06/1.00  
% 3.06/1.00  --bmc1_incremental                      false
% 3.06/1.00  --bmc1_axioms                           reachable_all
% 3.06/1.00  --bmc1_min_bound                        0
% 3.06/1.00  --bmc1_max_bound                        -1
% 3.06/1.00  --bmc1_max_bound_default                -1
% 3.06/1.00  --bmc1_symbol_reachability              true
% 3.06/1.00  --bmc1_property_lemmas                  false
% 3.06/1.00  --bmc1_k_induction                      false
% 3.06/1.00  --bmc1_non_equiv_states                 false
% 3.06/1.00  --bmc1_deadlock                         false
% 3.06/1.00  --bmc1_ucm                              false
% 3.06/1.00  --bmc1_add_unsat_core                   none
% 3.06/1.00  --bmc1_unsat_core_children              false
% 3.06/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.06/1.00  --bmc1_out_stat                         full
% 3.06/1.00  --bmc1_ground_init                      false
% 3.06/1.00  --bmc1_pre_inst_next_state              false
% 3.06/1.00  --bmc1_pre_inst_state                   false
% 3.06/1.00  --bmc1_pre_inst_reach_state             false
% 3.06/1.00  --bmc1_out_unsat_core                   false
% 3.06/1.00  --bmc1_aig_witness_out                  false
% 3.06/1.00  --bmc1_verbose                          false
% 3.06/1.00  --bmc1_dump_clauses_tptp                false
% 3.06/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.06/1.00  --bmc1_dump_file                        -
% 3.06/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.06/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.06/1.00  --bmc1_ucm_extend_mode                  1
% 3.06/1.00  --bmc1_ucm_init_mode                    2
% 3.06/1.00  --bmc1_ucm_cone_mode                    none
% 3.06/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.06/1.00  --bmc1_ucm_relax_model                  4
% 3.06/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.06/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.06/1.00  --bmc1_ucm_layered_model                none
% 3.06/1.00  --bmc1_ucm_max_lemma_size               10
% 3.06/1.00  
% 3.06/1.00  ------ AIG Options
% 3.06/1.00  
% 3.06/1.00  --aig_mode                              false
% 3.06/1.00  
% 3.06/1.00  ------ Instantiation Options
% 3.06/1.00  
% 3.06/1.00  --instantiation_flag                    true
% 3.06/1.00  --inst_sos_flag                         false
% 3.06/1.00  --inst_sos_phase                        true
% 3.06/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.06/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.06/1.00  --inst_lit_sel_side                     none
% 3.06/1.00  --inst_solver_per_active                1400
% 3.06/1.00  --inst_solver_calls_frac                1.
% 3.06/1.00  --inst_passive_queue_type               priority_queues
% 3.06/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.06/1.00  --inst_passive_queues_freq              [25;2]
% 3.06/1.00  --inst_dismatching                      true
% 3.06/1.00  --inst_eager_unprocessed_to_passive     true
% 3.06/1.00  --inst_prop_sim_given                   true
% 3.06/1.00  --inst_prop_sim_new                     false
% 3.06/1.00  --inst_subs_new                         false
% 3.06/1.00  --inst_eq_res_simp                      false
% 3.06/1.00  --inst_subs_given                       false
% 3.06/1.00  --inst_orphan_elimination               true
% 3.06/1.00  --inst_learning_loop_flag               true
% 3.06/1.00  --inst_learning_start                   3000
% 3.06/1.00  --inst_learning_factor                  2
% 3.06/1.00  --inst_start_prop_sim_after_learn       3
% 3.06/1.00  --inst_sel_renew                        solver
% 3.06/1.00  --inst_lit_activity_flag                true
% 3.06/1.00  --inst_restr_to_given                   false
% 3.06/1.00  --inst_activity_threshold               500
% 3.06/1.00  --inst_out_proof                        true
% 3.06/1.00  
% 3.06/1.00  ------ Resolution Options
% 3.06/1.00  
% 3.06/1.00  --resolution_flag                       false
% 3.06/1.00  --res_lit_sel                           adaptive
% 3.06/1.00  --res_lit_sel_side                      none
% 3.06/1.00  --res_ordering                          kbo
% 3.06/1.00  --res_to_prop_solver                    active
% 3.06/1.00  --res_prop_simpl_new                    false
% 3.06/1.00  --res_prop_simpl_given                  true
% 3.06/1.00  --res_passive_queue_type                priority_queues
% 3.06/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.06/1.00  --res_passive_queues_freq               [15;5]
% 3.06/1.00  --res_forward_subs                      full
% 3.06/1.00  --res_backward_subs                     full
% 3.06/1.00  --res_forward_subs_resolution           true
% 3.06/1.00  --res_backward_subs_resolution          true
% 3.06/1.00  --res_orphan_elimination                true
% 3.06/1.00  --res_time_limit                        2.
% 3.06/1.00  --res_out_proof                         true
% 3.06/1.00  
% 3.06/1.00  ------ Superposition Options
% 3.06/1.00  
% 3.06/1.00  --superposition_flag                    true
% 3.06/1.00  --sup_passive_queue_type                priority_queues
% 3.06/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.06/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.06/1.00  --demod_completeness_check              fast
% 3.06/1.00  --demod_use_ground                      true
% 3.06/1.00  --sup_to_prop_solver                    passive
% 3.06/1.00  --sup_prop_simpl_new                    true
% 3.06/1.00  --sup_prop_simpl_given                  true
% 3.06/1.00  --sup_fun_splitting                     false
% 3.06/1.00  --sup_smt_interval                      50000
% 3.06/1.00  
% 3.06/1.00  ------ Superposition Simplification Setup
% 3.06/1.00  
% 3.06/1.00  --sup_indices_passive                   []
% 3.06/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.06/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/1.00  --sup_full_bw                           [BwDemod]
% 3.06/1.00  --sup_immed_triv                        [TrivRules]
% 3.06/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.06/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/1.00  --sup_immed_bw_main                     []
% 3.06/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.06/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.06/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.06/1.00  
% 3.06/1.00  ------ Combination Options
% 3.06/1.00  
% 3.06/1.00  --comb_res_mult                         3
% 3.06/1.00  --comb_sup_mult                         2
% 3.06/1.00  --comb_inst_mult                        10
% 3.06/1.00  
% 3.06/1.00  ------ Debug Options
% 3.06/1.00  
% 3.06/1.00  --dbg_backtrace                         false
% 3.06/1.00  --dbg_dump_prop_clauses                 false
% 3.06/1.00  --dbg_dump_prop_clauses_file            -
% 3.06/1.00  --dbg_out_stat                          false
% 3.06/1.00  
% 3.06/1.00  
% 3.06/1.00  
% 3.06/1.00  
% 3.06/1.00  ------ Proving...
% 3.06/1.00  
% 3.06/1.00  
% 3.06/1.00  % SZS status Theorem for theBenchmark.p
% 3.06/1.00  
% 3.06/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.06/1.00  
% 3.06/1.00  fof(f23,conjecture,(
% 3.06/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 3.06/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f24,negated_conjecture,(
% 3.06/1.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 3.06/1.00    inference(negated_conjecture,[],[f23])).
% 3.06/1.00  
% 3.06/1.00  fof(f38,plain,(
% 3.06/1.00    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 3.06/1.00    inference(ennf_transformation,[],[f24])).
% 3.06/1.00  
% 3.06/1.00  fof(f39,plain,(
% 3.06/1.00    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 3.06/1.00    inference(flattening,[],[f38])).
% 3.06/1.00  
% 3.06/1.00  fof(f54,plain,(
% 3.06/1.00    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (k1_funct_1(sK6,sK5) != sK4 & r2_hidden(sK5,sK3) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4)))) & v1_funct_2(sK6,sK3,k1_tarski(sK4)) & v1_funct_1(sK6))),
% 3.06/1.00    introduced(choice_axiom,[])).
% 3.06/1.00  
% 3.06/1.00  fof(f55,plain,(
% 3.06/1.00    k1_funct_1(sK6,sK5) != sK4 & r2_hidden(sK5,sK3) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4)))) & v1_funct_2(sK6,sK3,k1_tarski(sK4)) & v1_funct_1(sK6)),
% 3.06/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f39,f54])).
% 3.06/1.00  
% 3.06/1.00  fof(f98,plain,(
% 3.06/1.00    r2_hidden(sK5,sK3)),
% 3.06/1.00    inference(cnf_transformation,[],[f55])).
% 3.06/1.00  
% 3.06/1.00  fof(f96,plain,(
% 3.06/1.00    v1_funct_2(sK6,sK3,k1_tarski(sK4))),
% 3.06/1.00    inference(cnf_transformation,[],[f55])).
% 3.06/1.00  
% 3.06/1.00  fof(f8,axiom,(
% 3.06/1.00    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.06/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f74,plain,(
% 3.06/1.00    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.06/1.00    inference(cnf_transformation,[],[f8])).
% 3.06/1.00  
% 3.06/1.00  fof(f9,axiom,(
% 3.06/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.06/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f75,plain,(
% 3.06/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.06/1.00    inference(cnf_transformation,[],[f9])).
% 3.06/1.00  
% 3.06/1.00  fof(f10,axiom,(
% 3.06/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.06/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f76,plain,(
% 3.06/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.06/1.00    inference(cnf_transformation,[],[f10])).
% 3.06/1.00  
% 3.06/1.00  fof(f11,axiom,(
% 3.06/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.06/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f77,plain,(
% 3.06/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.06/1.00    inference(cnf_transformation,[],[f11])).
% 3.06/1.00  
% 3.06/1.00  fof(f12,axiom,(
% 3.06/1.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.06/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f78,plain,(
% 3.06/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.06/1.00    inference(cnf_transformation,[],[f12])).
% 3.06/1.00  
% 3.06/1.00  fof(f13,axiom,(
% 3.06/1.00    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.06/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f79,plain,(
% 3.06/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.06/1.00    inference(cnf_transformation,[],[f13])).
% 3.06/1.00  
% 3.06/1.00  fof(f14,axiom,(
% 3.06/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.06/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f80,plain,(
% 3.06/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.06/1.00    inference(cnf_transformation,[],[f14])).
% 3.06/1.00  
% 3.06/1.00  fof(f100,plain,(
% 3.06/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.06/1.00    inference(definition_unfolding,[],[f79,f80])).
% 3.06/1.00  
% 3.06/1.00  fof(f101,plain,(
% 3.06/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.06/1.00    inference(definition_unfolding,[],[f78,f100])).
% 3.06/1.00  
% 3.06/1.00  fof(f102,plain,(
% 3.06/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.06/1.00    inference(definition_unfolding,[],[f77,f101])).
% 3.06/1.00  
% 3.06/1.00  fof(f103,plain,(
% 3.06/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.06/1.00    inference(definition_unfolding,[],[f76,f102])).
% 3.06/1.00  
% 3.06/1.00  fof(f104,plain,(
% 3.06/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.06/1.00    inference(definition_unfolding,[],[f75,f103])).
% 3.06/1.00  
% 3.06/1.00  fof(f105,plain,(
% 3.06/1.00    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.06/1.00    inference(definition_unfolding,[],[f74,f104])).
% 3.06/1.00  
% 3.06/1.00  fof(f120,plain,(
% 3.06/1.00    v1_funct_2(sK6,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),
% 3.06/1.00    inference(definition_unfolding,[],[f96,f105])).
% 3.06/1.00  
% 3.06/1.00  fof(f22,axiom,(
% 3.06/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.06/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f36,plain,(
% 3.06/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.06/1.00    inference(ennf_transformation,[],[f22])).
% 3.06/1.00  
% 3.06/1.00  fof(f37,plain,(
% 3.06/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.06/1.00    inference(flattening,[],[f36])).
% 3.06/1.00  
% 3.06/1.00  fof(f53,plain,(
% 3.06/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.06/1.00    inference(nnf_transformation,[],[f37])).
% 3.06/1.00  
% 3.06/1.00  fof(f89,plain,(
% 3.06/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.06/1.00    inference(cnf_transformation,[],[f53])).
% 3.06/1.00  
% 3.06/1.00  fof(f97,plain,(
% 3.06/1.00    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4))))),
% 3.06/1.00    inference(cnf_transformation,[],[f55])).
% 3.06/1.00  
% 3.06/1.00  fof(f119,plain,(
% 3.06/1.00    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))),
% 3.06/1.00    inference(definition_unfolding,[],[f97,f105])).
% 3.06/1.00  
% 3.06/1.00  fof(f20,axiom,(
% 3.06/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.06/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f34,plain,(
% 3.06/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.06/1.00    inference(ennf_transformation,[],[f20])).
% 3.06/1.00  
% 3.06/1.00  fof(f87,plain,(
% 3.06/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.06/1.00    inference(cnf_transformation,[],[f34])).
% 3.06/1.00  
% 3.06/1.00  fof(f15,axiom,(
% 3.06/1.00    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 3.06/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f50,plain,(
% 3.06/1.00    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 3.06/1.00    inference(nnf_transformation,[],[f15])).
% 3.06/1.00  
% 3.06/1.00  fof(f81,plain,(
% 3.06/1.00    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 3.06/1.00    inference(cnf_transformation,[],[f50])).
% 3.06/1.00  
% 3.06/1.00  fof(f118,plain,(
% 3.06/1.00    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.06/1.00    inference(definition_unfolding,[],[f81,f105,f105,f105])).
% 3.06/1.00  
% 3.06/1.00  fof(f127,plain,(
% 3.06/1.00    ( ! [X1] : (k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) )),
% 3.06/1.00    inference(equality_resolution,[],[f118])).
% 3.06/1.00  
% 3.06/1.00  fof(f4,axiom,(
% 3.06/1.00    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.06/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f67,plain,(
% 3.06/1.00    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.06/1.00    inference(cnf_transformation,[],[f4])).
% 3.06/1.00  
% 3.06/1.00  fof(f18,axiom,(
% 3.06/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.06/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f32,plain,(
% 3.06/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.06/1.00    inference(ennf_transformation,[],[f18])).
% 3.06/1.00  
% 3.06/1.00  fof(f85,plain,(
% 3.06/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.06/1.00    inference(cnf_transformation,[],[f32])).
% 3.06/1.00  
% 3.06/1.00  fof(f17,axiom,(
% 3.06/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 3.06/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f30,plain,(
% 3.06/1.00    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.06/1.00    inference(ennf_transformation,[],[f17])).
% 3.06/1.00  
% 3.06/1.00  fof(f31,plain,(
% 3.06/1.00    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.06/1.00    inference(flattening,[],[f30])).
% 3.06/1.00  
% 3.06/1.00  fof(f84,plain,(
% 3.06/1.00    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.06/1.00    inference(cnf_transformation,[],[f31])).
% 3.06/1.00  
% 3.06/1.00  fof(f95,plain,(
% 3.06/1.00    v1_funct_1(sK6)),
% 3.06/1.00    inference(cnf_transformation,[],[f55])).
% 3.06/1.00  
% 3.06/1.00  fof(f16,axiom,(
% 3.06/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k2_relat_1(X1)) => r2_hidden(X2,X0)))),
% 3.06/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f28,plain,(
% 3.06/1.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,k2_relat_1(X1))) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.06/1.00    inference(ennf_transformation,[],[f16])).
% 3.06/1.00  
% 3.06/1.00  fof(f29,plain,(
% 3.06/1.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,k2_relat_1(X1))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.06/1.00    inference(flattening,[],[f28])).
% 3.06/1.00  
% 3.06/1.00  fof(f83,plain,(
% 3.06/1.00    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,k2_relat_1(X1)) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.06/1.00    inference(cnf_transformation,[],[f29])).
% 3.06/1.00  
% 3.06/1.00  fof(f19,axiom,(
% 3.06/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.06/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f26,plain,(
% 3.06/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.06/1.00    inference(pure_predicate_removal,[],[f19])).
% 3.06/1.00  
% 3.06/1.00  fof(f33,plain,(
% 3.06/1.00    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.06/1.00    inference(ennf_transformation,[],[f26])).
% 3.06/1.00  
% 3.06/1.00  fof(f86,plain,(
% 3.06/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.06/1.00    inference(cnf_transformation,[],[f33])).
% 3.06/1.00  
% 3.06/1.00  fof(f7,axiom,(
% 3.06/1.00    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.06/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f46,plain,(
% 3.06/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.06/1.00    inference(nnf_transformation,[],[f7])).
% 3.06/1.00  
% 3.06/1.00  fof(f47,plain,(
% 3.06/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.06/1.00    inference(rectify,[],[f46])).
% 3.06/1.00  
% 3.06/1.00  fof(f48,plain,(
% 3.06/1.00    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 3.06/1.00    introduced(choice_axiom,[])).
% 3.06/1.00  
% 3.06/1.00  fof(f49,plain,(
% 3.06/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.06/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f47,f48])).
% 3.06/1.00  
% 3.06/1.00  fof(f70,plain,(
% 3.06/1.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.06/1.00    inference(cnf_transformation,[],[f49])).
% 3.06/1.00  
% 3.06/1.00  fof(f116,plain,(
% 3.06/1.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 3.06/1.00    inference(definition_unfolding,[],[f70,f105])).
% 3.06/1.00  
% 3.06/1.00  fof(f126,plain,(
% 3.06/1.00    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) )),
% 3.06/1.00    inference(equality_resolution,[],[f116])).
% 3.06/1.00  
% 3.06/1.00  fof(f99,plain,(
% 3.06/1.00    k1_funct_1(sK6,sK5) != sK4),
% 3.06/1.00    inference(cnf_transformation,[],[f55])).
% 3.06/1.00  
% 3.06/1.00  cnf(c_32,negated_conjecture,
% 3.06/1.00      ( r2_hidden(sK5,sK3) ),
% 3.06/1.00      inference(cnf_transformation,[],[f98]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1122,plain,
% 3.06/1.00      ( r2_hidden(sK5,sK3) = iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_34,negated_conjecture,
% 3.06/1.00      ( v1_funct_2(sK6,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
% 3.06/1.00      inference(cnf_transformation,[],[f120]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_30,plain,
% 3.06/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.06/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.06/1.00      | k1_xboole_0 = X2 ),
% 3.06/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_33,negated_conjecture,
% 3.06/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) ),
% 3.06/1.00      inference(cnf_transformation,[],[f119]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_424,plain,
% 3.06/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.06/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.06/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 3.06/1.00      | sK6 != X0
% 3.06/1.00      | k1_xboole_0 = X2 ),
% 3.06/1.00      inference(resolution_lifted,[status(thm)],[c_30,c_33]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_425,plain,
% 3.06/1.00      ( ~ v1_funct_2(sK6,X0,X1)
% 3.06/1.00      | k1_relset_1(X0,X1,sK6) = X0
% 3.06/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.06/1.00      | k1_xboole_0 = X1 ),
% 3.06/1.00      inference(unflattening,[status(thm)],[c_424]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_598,plain,
% 3.06/1.00      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != X0
% 3.06/1.00      | k1_relset_1(X1,X0,sK6) = X1
% 3.06/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0))
% 3.06/1.00      | sK3 != X1
% 3.06/1.00      | sK6 != sK6
% 3.06/1.00      | k1_xboole_0 = X0 ),
% 3.06/1.00      inference(resolution_lifted,[status(thm)],[c_34,c_425]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_599,plain,
% 3.06/1.00      ( k1_relset_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK6) = sK3
% 3.06/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))
% 3.06/1.00      | k1_xboole_0 = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 3.06/1.00      inference(unflattening,[status(thm)],[c_598]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_670,plain,
% 3.06/1.00      ( k1_relset_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK6) = sK3
% 3.06/1.00      | k1_xboole_0 = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 3.06/1.00      inference(equality_resolution_simp,[status(thm)],[c_599]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_23,plain,
% 3.06/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.06/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_460,plain,
% 3.06/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.06/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.06/1.00      | sK6 != X2 ),
% 3.06/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_33]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_461,plain,
% 3.06/1.00      ( k1_relset_1(X0,X1,sK6) = k1_relat_1(sK6)
% 3.06/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 3.06/1.00      inference(unflattening,[status(thm)],[c_460]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1326,plain,
% 3.06/1.00      ( k1_relset_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK6) = k1_relat_1(sK6) ),
% 3.06/1.00      inference(equality_resolution,[status(thm)],[c_461]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1426,plain,
% 3.06/1.00      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k1_xboole_0
% 3.06/1.00      | k1_relat_1(sK6) = sK3 ),
% 3.06/1.00      inference(demodulation,[status(thm)],[c_670,c_1326]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1433,plain,
% 3.06/1.00      ( k1_relset_1(X0,X1,sK6) = k1_relat_1(sK6)
% 3.06/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))
% 3.06/1.00      | k1_relat_1(sK6) = sK3 ),
% 3.06/1.00      inference(superposition,[status(thm)],[c_1426,c_461]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_18,plain,
% 3.06/1.00      ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 3.06/1.00      inference(cnf_transformation,[],[f127]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1764,plain,
% 3.06/1.00      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k4_xboole_0(k1_xboole_0,k1_xboole_0)
% 3.06/1.00      | k1_relat_1(sK6) = sK3 ),
% 3.06/1.00      inference(superposition,[status(thm)],[c_1426,c_18]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_11,plain,
% 3.06/1.00      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.06/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1766,plain,
% 3.06/1.00      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k1_xboole_0
% 3.06/1.00      | k1_relat_1(sK6) = sK3 ),
% 3.06/1.00      inference(demodulation,[status(thm)],[c_1764,c_11]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1767,plain,
% 3.06/1.00      ( k1_relat_1(sK6) = sK3 ),
% 3.06/1.00      inference(global_propositional_subsumption,
% 3.06/1.00                [status(thm)],
% 3.06/1.00                [c_1433,c_1426,c_1766]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_21,plain,
% 3.06/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.00      | v1_relat_1(X0) ),
% 3.06/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_20,plain,
% 3.06/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.06/1.00      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 3.06/1.00      | ~ v1_funct_1(X1)
% 3.06/1.00      | ~ v1_relat_1(X1) ),
% 3.06/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_35,negated_conjecture,
% 3.06/1.00      ( v1_funct_1(sK6) ),
% 3.06/1.00      inference(cnf_transformation,[],[f95]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_346,plain,
% 3.06/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.06/1.00      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 3.06/1.00      | ~ v1_relat_1(X1)
% 3.06/1.00      | sK6 != X1 ),
% 3.06/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_35]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_347,plain,
% 3.06/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK6))
% 3.06/1.00      | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6))
% 3.06/1.00      | ~ v1_relat_1(sK6) ),
% 3.06/1.00      inference(unflattening,[status(thm)],[c_346]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_390,plain,
% 3.06/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.00      | ~ r2_hidden(X3,k1_relat_1(sK6))
% 3.06/1.00      | r2_hidden(k1_funct_1(sK6,X3),k2_relat_1(sK6))
% 3.06/1.00      | sK6 != X0 ),
% 3.06/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_347]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_391,plain,
% 3.06/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.06/1.00      | ~ r2_hidden(X2,k1_relat_1(sK6))
% 3.06/1.00      | r2_hidden(k1_funct_1(sK6,X2),k2_relat_1(sK6)) ),
% 3.06/1.00      inference(unflattening,[status(thm)],[c_390]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_534,plain,
% 3.06/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK6))
% 3.06/1.00      | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6))
% 3.06/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 3.06/1.00      | sK6 != sK6 ),
% 3.06/1.00      inference(resolution_lifted,[status(thm)],[c_33,c_391]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_671,plain,
% 3.06/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK6))
% 3.06/1.00      | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6))
% 3.06/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
% 3.06/1.00      inference(equality_resolution_simp,[status(thm)],[c_534]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_782,plain,
% 3.06/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK6))
% 3.06/1.00      | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6))
% 3.06/1.00      | ~ sP1_iProver_split ),
% 3.06/1.00      inference(splitting,
% 3.06/1.00                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 3.06/1.00                [c_671]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1119,plain,
% 3.06/1.00      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 3.06/1.00      | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top
% 3.06/1.00      | sP1_iProver_split != iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_782]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1770,plain,
% 3.06/1.00      ( r2_hidden(X0,sK3) != iProver_top
% 3.06/1.00      | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top
% 3.06/1.00      | sP1_iProver_split != iProver_top ),
% 3.06/1.00      inference(demodulation,[status(thm)],[c_1767,c_1119]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_19,plain,
% 3.06/1.00      ( ~ v5_relat_1(X0,X1)
% 3.06/1.00      | r2_hidden(X2,X1)
% 3.06/1.00      | ~ r2_hidden(X2,k2_relat_1(X0))
% 3.06/1.00      | ~ v1_relat_1(X0) ),
% 3.06/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_22,plain,
% 3.06/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.00      | v5_relat_1(X0,X2) ),
% 3.06/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_365,plain,
% 3.06/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.00      | r2_hidden(X3,X4)
% 3.06/1.00      | ~ r2_hidden(X3,k2_relat_1(X5))
% 3.06/1.00      | ~ v1_relat_1(X5)
% 3.06/1.00      | X0 != X5
% 3.06/1.00      | X2 != X4 ),
% 3.06/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_22]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_366,plain,
% 3.06/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.00      | r2_hidden(X3,X2)
% 3.06/1.00      | ~ r2_hidden(X3,k2_relat_1(X0))
% 3.06/1.00      | ~ v1_relat_1(X0) ),
% 3.06/1.00      inference(unflattening,[status(thm)],[c_365]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_370,plain,
% 3.06/1.00      ( ~ r2_hidden(X3,k2_relat_1(X0))
% 3.06/1.00      | r2_hidden(X3,X2)
% 3.06/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.06/1.00      inference(global_propositional_subsumption,
% 3.06/1.00                [status(thm)],
% 3.06/1.00                [c_366,c_21]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_371,plain,
% 3.06/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.00      | r2_hidden(X3,X2)
% 3.06/1.00      | ~ r2_hidden(X3,k2_relat_1(X0)) ),
% 3.06/1.00      inference(renaming,[status(thm)],[c_370]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_409,plain,
% 3.06/1.00      ( r2_hidden(X0,X1)
% 3.06/1.00      | ~ r2_hidden(X0,k2_relat_1(X2))
% 3.06/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X3,X1))
% 3.06/1.00      | sK6 != X2 ),
% 3.06/1.00      inference(resolution_lifted,[status(thm)],[c_371,c_33]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_410,plain,
% 3.06/1.00      ( r2_hidden(X0,X1)
% 3.06/1.00      | ~ r2_hidden(X0,k2_relat_1(sK6))
% 3.06/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X2,X1)) ),
% 3.06/1.00      inference(unflattening,[status(thm)],[c_409]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1121,plain,
% 3.06/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.06/1.00      | r2_hidden(X2,X1) = iProver_top
% 3.06/1.00      | r2_hidden(X2,k2_relat_1(sK6)) != iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_410]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1422,plain,
% 3.06/1.00      ( r2_hidden(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top
% 3.06/1.00      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
% 3.06/1.00      inference(equality_resolution,[status(thm)],[c_1121]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_16,plain,
% 3.06/1.00      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | X0 = X1 ),
% 3.06/1.00      inference(cnf_transformation,[],[f126]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1124,plain,
% 3.06/1.00      ( X0 = X1
% 3.06/1.00      | r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_3231,plain,
% 3.06/1.00      ( sK4 = X0 | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
% 3.06/1.00      inference(superposition,[status(thm)],[c_1422,c_1124]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_3779,plain,
% 3.06/1.00      ( k1_funct_1(sK6,X0) = sK4
% 3.06/1.00      | r2_hidden(X0,sK3) != iProver_top
% 3.06/1.00      | sP1_iProver_split != iProver_top ),
% 3.06/1.00      inference(superposition,[status(thm)],[c_1770,c_3231]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_783,plain,
% 3.06/1.00      ( sP1_iProver_split | sP0_iProver_split ),
% 3.06/1.00      inference(splitting,
% 3.06/1.00                [splitting(split),new_symbols(definition,[])],
% 3.06/1.00                [c_671]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_809,plain,
% 3.06/1.00      ( sP1_iProver_split = iProver_top
% 3.06/1.00      | sP0_iProver_split = iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_783]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_781,plain,
% 3.06/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.06/1.00      | ~ sP0_iProver_split ),
% 3.06/1.00      inference(splitting,
% 3.06/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.06/1.00                [c_671]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1120,plain,
% 3.06/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.06/1.00      | sP0_iProver_split != iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_781]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2304,plain,
% 3.06/1.00      ( sP0_iProver_split != iProver_top ),
% 3.06/1.00      inference(equality_resolution,[status(thm)],[c_1120]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_3794,plain,
% 3.06/1.00      ( r2_hidden(X0,sK3) != iProver_top | k1_funct_1(sK6,X0) = sK4 ),
% 3.06/1.00      inference(global_propositional_subsumption,
% 3.06/1.00                [status(thm)],
% 3.06/1.00                [c_3779,c_809,c_2304]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_3795,plain,
% 3.06/1.00      ( k1_funct_1(sK6,X0) = sK4 | r2_hidden(X0,sK3) != iProver_top ),
% 3.06/1.00      inference(renaming,[status(thm)],[c_3794]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_3803,plain,
% 3.06/1.00      ( k1_funct_1(sK6,sK5) = sK4 ),
% 3.06/1.00      inference(superposition,[status(thm)],[c_1122,c_3795]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_31,negated_conjecture,
% 3.06/1.00      ( k1_funct_1(sK6,sK5) != sK4 ),
% 3.06/1.00      inference(cnf_transformation,[],[f99]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(contradiction,plain,
% 3.06/1.00      ( $false ),
% 3.06/1.00      inference(minisat,[status(thm)],[c_3803,c_31]) ).
% 3.06/1.00  
% 3.06/1.00  
% 3.06/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.06/1.00  
% 3.06/1.00  ------                               Statistics
% 3.06/1.00  
% 3.06/1.00  ------ General
% 3.06/1.00  
% 3.06/1.00  abstr_ref_over_cycles:                  0
% 3.06/1.00  abstr_ref_under_cycles:                 0
% 3.06/1.00  gc_basic_clause_elim:                   0
% 3.06/1.00  forced_gc_time:                         0
% 3.06/1.00  parsing_time:                           0.014
% 3.06/1.00  unif_index_cands_time:                  0.
% 3.06/1.00  unif_index_add_time:                    0.
% 3.06/1.00  orderings_time:                         0.
% 3.06/1.00  out_proof_time:                         0.009
% 3.06/1.00  total_time:                             0.177
% 3.06/1.00  num_of_symbols:                         56
% 3.06/1.00  num_of_terms:                           3579
% 3.06/1.00  
% 3.06/1.00  ------ Preprocessing
% 3.06/1.00  
% 3.06/1.00  num_of_splits:                          2
% 3.06/1.00  num_of_split_atoms:                     2
% 3.06/1.00  num_of_reused_defs:                     0
% 3.06/1.00  num_eq_ax_congr_red:                    28
% 3.06/1.00  num_of_sem_filtered_clauses:            1
% 3.06/1.00  num_of_subtypes:                        0
% 3.06/1.00  monotx_restored_types:                  0
% 3.06/1.00  sat_num_of_epr_types:                   0
% 3.06/1.00  sat_num_of_non_cyclic_types:            0
% 3.06/1.00  sat_guarded_non_collapsed_types:        0
% 3.06/1.00  num_pure_diseq_elim:                    0
% 3.06/1.00  simp_replaced_by:                       0
% 3.06/1.00  res_preprocessed:                       149
% 3.06/1.00  prep_upred:                             0
% 3.06/1.00  prep_unflattend:                        28
% 3.06/1.00  smt_new_axioms:                         0
% 3.06/1.00  pred_elim_cands:                        1
% 3.06/1.00  pred_elim:                              5
% 3.06/1.00  pred_elim_cl:                           8
% 3.06/1.00  pred_elim_cycles:                       7
% 3.06/1.00  merged_defs:                            0
% 3.06/1.00  merged_defs_ncl:                        0
% 3.06/1.00  bin_hyper_res:                          0
% 3.06/1.00  prep_cycles:                            4
% 3.06/1.00  pred_elim_time:                         0.01
% 3.06/1.00  splitting_time:                         0.
% 3.06/1.00  sem_filter_time:                        0.
% 3.06/1.00  monotx_time:                            0.001
% 3.06/1.00  subtype_inf_time:                       0.
% 3.06/1.00  
% 3.06/1.00  ------ Problem properties
% 3.06/1.00  
% 3.06/1.00  clauses:                                30
% 3.06/1.00  conjectures:                            2
% 3.06/1.00  epr:                                    2
% 3.06/1.00  horn:                                   19
% 3.06/1.00  ground:                                 6
% 3.06/1.00  unary:                                  7
% 3.06/1.00  binary:                                 9
% 3.06/1.00  lits:                                   69
% 3.06/1.00  lits_eq:                                29
% 3.06/1.00  fd_pure:                                0
% 3.06/1.00  fd_pseudo:                              0
% 3.06/1.00  fd_cond:                                1
% 3.06/1.00  fd_pseudo_cond:                         6
% 3.06/1.00  ac_symbols:                             0
% 3.06/1.00  
% 3.06/1.00  ------ Propositional Solver
% 3.06/1.00  
% 3.06/1.00  prop_solver_calls:                      26
% 3.06/1.00  prop_fast_solver_calls:                 880
% 3.06/1.00  smt_solver_calls:                       0
% 3.06/1.00  smt_fast_solver_calls:                  0
% 3.06/1.00  prop_num_of_clauses:                    1336
% 3.06/1.00  prop_preprocess_simplified:             5689
% 3.06/1.00  prop_fo_subsumed:                       13
% 3.06/1.00  prop_solver_time:                       0.
% 3.06/1.00  smt_solver_time:                        0.
% 3.06/1.00  smt_fast_solver_time:                   0.
% 3.06/1.00  prop_fast_solver_time:                  0.
% 3.06/1.00  prop_unsat_core_time:                   0.
% 3.06/1.00  
% 3.06/1.00  ------ QBF
% 3.06/1.00  
% 3.06/1.00  qbf_q_res:                              0
% 3.06/1.00  qbf_num_tautologies:                    0
% 3.06/1.00  qbf_prep_cycles:                        0
% 3.06/1.00  
% 3.06/1.00  ------ BMC1
% 3.06/1.00  
% 3.06/1.00  bmc1_current_bound:                     -1
% 3.06/1.00  bmc1_last_solved_bound:                 -1
% 3.06/1.00  bmc1_unsat_core_size:                   -1
% 3.06/1.00  bmc1_unsat_core_parents_size:           -1
% 3.06/1.00  bmc1_merge_next_fun:                    0
% 3.06/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.06/1.00  
% 3.06/1.00  ------ Instantiation
% 3.06/1.00  
% 3.06/1.00  inst_num_of_clauses:                    376
% 3.06/1.00  inst_num_in_passive:                    258
% 3.06/1.00  inst_num_in_active:                     108
% 3.06/1.00  inst_num_in_unprocessed:                10
% 3.06/1.00  inst_num_of_loops:                      180
% 3.06/1.00  inst_num_of_learning_restarts:          0
% 3.06/1.00  inst_num_moves_active_passive:          71
% 3.06/1.00  inst_lit_activity:                      0
% 3.06/1.00  inst_lit_activity_moves:                0
% 3.06/1.00  inst_num_tautologies:                   0
% 3.06/1.00  inst_num_prop_implied:                  0
% 3.06/1.00  inst_num_existing_simplified:           0
% 3.06/1.00  inst_num_eq_res_simplified:             0
% 3.06/1.00  inst_num_child_elim:                    0
% 3.06/1.00  inst_num_of_dismatching_blockings:      154
% 3.06/1.00  inst_num_of_non_proper_insts:           286
% 3.06/1.00  inst_num_of_duplicates:                 0
% 3.06/1.00  inst_inst_num_from_inst_to_res:         0
% 3.06/1.00  inst_dismatching_checking_time:         0.
% 3.06/1.00  
% 3.06/1.00  ------ Resolution
% 3.06/1.00  
% 3.06/1.00  res_num_of_clauses:                     0
% 3.06/1.00  res_num_in_passive:                     0
% 3.06/1.00  res_num_in_active:                      0
% 3.06/1.00  res_num_of_loops:                       153
% 3.06/1.00  res_forward_subset_subsumed:            35
% 3.06/1.00  res_backward_subset_subsumed:           0
% 3.06/1.00  res_forward_subsumed:                   0
% 3.06/1.00  res_backward_subsumed:                  0
% 3.06/1.00  res_forward_subsumption_resolution:     0
% 3.06/1.00  res_backward_subsumption_resolution:    0
% 3.06/1.00  res_clause_to_clause_subsumption:       93
% 3.06/1.00  res_orphan_elimination:                 0
% 3.06/1.00  res_tautology_del:                      14
% 3.06/1.00  res_num_eq_res_simplified:              2
% 3.06/1.00  res_num_sel_changes:                    0
% 3.06/1.00  res_moves_from_active_to_pass:          0
% 3.06/1.00  
% 3.06/1.00  ------ Superposition
% 3.06/1.00  
% 3.06/1.00  sup_time_total:                         0.
% 3.06/1.00  sup_time_generating:                    0.
% 3.06/1.00  sup_time_sim_full:                      0.
% 3.06/1.00  sup_time_sim_immed:                     0.
% 3.06/1.00  
% 3.06/1.00  sup_num_of_clauses:                     53
% 3.06/1.00  sup_num_in_active:                      32
% 3.06/1.00  sup_num_in_passive:                     21
% 3.06/1.00  sup_num_of_loops:                       35
% 3.06/1.00  sup_fw_superposition:                   43
% 3.06/1.00  sup_bw_superposition:                   9
% 3.06/1.00  sup_immediate_simplified:               14
% 3.06/1.00  sup_given_eliminated:                   1
% 3.06/1.00  comparisons_done:                       0
% 3.06/1.00  comparisons_avoided:                    5
% 3.06/1.00  
% 3.06/1.00  ------ Simplifications
% 3.06/1.00  
% 3.06/1.00  
% 3.06/1.00  sim_fw_subset_subsumed:                 8
% 3.06/1.00  sim_bw_subset_subsumed:                 1
% 3.06/1.00  sim_fw_subsumed:                        2
% 3.06/1.00  sim_bw_subsumed:                        2
% 3.06/1.00  sim_fw_subsumption_res:                 1
% 3.06/1.00  sim_bw_subsumption_res:                 0
% 3.06/1.00  sim_tautology_del:                      9
% 3.06/1.00  sim_eq_tautology_del:                   4
% 3.06/1.00  sim_eq_res_simp:                        0
% 3.06/1.00  sim_fw_demodulated:                     2
% 3.06/1.00  sim_bw_demodulated:                     3
% 3.06/1.00  sim_light_normalised:                   1
% 3.06/1.00  sim_joinable_taut:                      0
% 3.06/1.00  sim_joinable_simp:                      0
% 3.06/1.00  sim_ac_normalised:                      0
% 3.06/1.00  sim_smt_subsumption:                    0
% 3.06/1.00  
%------------------------------------------------------------------------------
