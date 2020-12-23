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
% DateTime   : Thu Dec  3 12:06:17 EST 2020

% Result     : Theorem 3.62s
% Output     : CNFRefutation 3.62s
% Verified   : 
% Statistics : Number of formulae       :  169 (3259 expanded)
%              Number of clauses        :   80 ( 525 expanded)
%              Number of leaves         :   24 ( 865 expanded)
%              Depth                    :   28
%              Number of atoms          :  531 (8134 expanded)
%              Number of equality atoms :  313 (4096 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f30,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f31,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f30])).

fof(f47,plain,
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

fof(f48,plain,
    ( k1_funct_1(sK6,sK5) != sK4
    & r2_hidden(sK5,sK3)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4))))
    & v1_funct_2(sK6,sK3,k1_tarski(sK4))
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f31,f47])).

fof(f94,plain,(
    r2_hidden(sK5,sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f92,plain,(
    v1_funct_2(sK6,sK3,k1_tarski(sK4)) ),
    inference(cnf_transformation,[],[f48])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f96,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f56,f57])).

fof(f97,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f55,f96])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f54,f97])).

fof(f99,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f53,f98])).

fof(f100,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f52,f99])).

fof(f101,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f51,f100])).

fof(f108,plain,(
    v1_funct_2(sK6,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(definition_unfolding,[],[f92,f101])).

fof(f18,axiom,(
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
    inference(ennf_transformation,[],[f18])).

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
    inference(flattening,[],[f28])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f93,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4)))) ),
    inference(cnf_transformation,[],[f48])).

fof(f107,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) ),
    inference(definition_unfolding,[],[f93,f101])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f121,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f89])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f44])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f118,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f78])).

fof(f91,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f48])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2)))
     => ( k2_mcart_1(X0) = X2
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k2_mcart_1(X0) = X2
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(X0) = X2
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(X0) = X2
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))) ) ),
    inference(definition_unfolding,[],[f82,f101])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f84,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f17])).

fof(f95,plain,(
    k1_funct_1(sK6,sK5) != sK4 ),
    inference(cnf_transformation,[],[f48])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f102,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f50,f49])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
        | r2_hidden(X0,X1) )
      & ( ~ r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f58,f49,f101,f101])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ~ ( X7 != X9
              & X6 != X9
              & X5 != X9
              & X4 != X9
              & X3 != X9
              & X2 != X9
              & X1 != X9
              & X0 != X9 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ( X7 = X9
            | X6 = X9
            | X5 = X9
            | X4 = X9
            | X3 = X9
            | X2 = X9
            | X1 = X9
            | X0 = X9 ) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f32,plain,(
    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
    <=> ( X7 = X9
        | X6 = X9
        | X5 = X9
        | X4 = X9
        | X3 = X9
        | X2 = X9
        | X1 = X9
        | X0 = X9 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(definition_folding,[],[f21,f33,f32])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) )
      & ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f73,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f117,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(equality_resolution,[],[f73])).

fof(f40,plain,(
    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
        | ( X7 != X9
          & X6 != X9
          & X5 != X9
          & X4 != X9
          & X3 != X9
          & X2 != X9
          & X1 != X9
          & X0 != X9 ) )
      & ( X7 = X9
        | X6 = X9
        | X5 = X9
        | X4 = X9
        | X3 = X9
        | X2 = X9
        | X1 = X9
        | X0 = X9
        | ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f41,plain,(
    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
        | ( X7 != X9
          & X6 != X9
          & X5 != X9
          & X4 != X9
          & X3 != X9
          & X2 != X9
          & X1 != X9
          & X0 != X9 ) )
      & ( X7 = X9
        | X6 = X9
        | X5 = X9
        | X4 = X9
        | X3 = X9
        | X2 = X9
        | X1 = X9
        | X0 = X9
        | ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(flattening,[],[f40])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3
          & X0 != X4
          & X0 != X5
          & X0 != X6
          & X0 != X7
          & X0 != X8 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | X0 = X4
        | X0 = X5
        | X0 = X6
        | X0 = X7
        | X0 = X8
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(rectify,[],[f41])).

fof(f72,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f109,plain,(
    ! [X6,X4,X2,X8,X7,X5,X3,X1] : sP0(X1,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(equality_resolution,[],[f72])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ? [X9] :
            ( ( ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X9,X8) )
            & ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X9] :
            ( ( r2_hidden(X9,X8)
              | ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X9,X8) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ? [X9] :
            ( ( ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X9,X8) )
            & ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X8)
              | ~ sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X10,X8) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X9] :
          ( ( ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(X9,X8) )
          & ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(X9,X8) ) )
     => ( ( ~ sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
          | ~ r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) )
        & ( sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
          | r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ( ( ~ sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) )
          & ( sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X8)
              | ~ sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X10,X8) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f38])).

fof(f61,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] :
      ( r2_hidden(X10,X8)
      | ~ sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_35,negated_conjecture,
    ( r2_hidden(sK5,sK3) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2874,plain,
    ( r2_hidden(sK5,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_37,negated_conjecture,
    ( v1_funct_2(sK6,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_33,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_600,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK6 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_36])).

cnf(c_601,plain,
    ( ~ v1_funct_2(sK6,X0,X1)
    | k1_relset_1(X0,X1,sK6) = X0
    | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_600])).

cnf(c_964,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != X0
    | k1_relset_1(X1,X0,sK6) = X1
    | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0))
    | sK3 != X1
    | sK6 != sK6
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_37,c_601])).

cnf(c_965,plain,
    ( k1_relset_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK6) = sK3
    | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))
    | k1_xboole_0 = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(unflattening,[status(thm)],[c_964])).

cnf(c_1438,plain,
    ( k1_relset_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK6) = sK3
    | k1_xboole_0 = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(equality_resolution_simp,[status(thm)],[c_965])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_636,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_36])).

cnf(c_637,plain,
    ( k1_relset_1(X0,X1,sK6) = k1_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_636])).

cnf(c_3100,plain,
    ( k1_relset_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK6) = k1_relat_1(sK6) ),
    inference(equality_resolution,[status(thm)],[c_637])).

cnf(c_3183,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k1_xboole_0
    | k1_relat_1(sK6) = sK3 ),
    inference(demodulation,[status(thm)],[c_1438,c_3100])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f121])).

cnf(c_674,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))
    | sK6 != X0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_36])).

cnf(c_675,plain,
    ( ~ v1_funct_2(sK6,X0,k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK6 ),
    inference(unflattening,[status(thm)],[c_674])).

cnf(c_975,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))
    | sK3 != X0
    | sK6 != sK6
    | sK6 = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_37,c_675])).

cnf(c_976,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))
    | sK6 = k1_xboole_0
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_975])).

cnf(c_3187,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k1_xboole_0
    | k1_relat_1(sK6) = sK3
    | sK3 = k1_xboole_0
    | sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3183,c_976])).

cnf(c_3208,plain,
    ( k1_relat_1(sK6) = sK3
    | sK3 = k1_xboole_0
    | sK6 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3187,c_3183])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_38,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_504,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_38])).

cnf(c_505,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK6))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6)
    | ~ v1_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_504])).

cnf(c_2871,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_505])).

cnf(c_506,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_505])).

cnf(c_2224,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3091,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) ),
    inference(instantiation,[status(thm)],[c_2224])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_645,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_36])).

cnf(c_646,plain,
    ( v1_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_645])).

cnf(c_3093,plain,
    ( v1_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) ),
    inference(instantiation,[status(thm)],[c_646])).

cnf(c_3094,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3093])).

cnf(c_3424,plain,
    ( r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2871,c_506,c_3091,c_3094])).

cnf(c_3425,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top ),
    inference(renaming,[status(thm)],[c_3424])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_585,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(X2)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_36])).

cnf(c_586,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,sK6)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(X1) ),
    inference(unflattening,[status(thm)],[c_585])).

cnf(c_2870,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(X0)
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X1,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_586])).

cnf(c_3439,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2870])).

cnf(c_24,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))
    | k2_mcart_1(X0) = X2 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_2876,plain,
    ( k2_mcart_1(X0) = X1
    | r2_hidden(X0,k2_zfmisc_1(X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_5543,plain,
    ( k2_mcart_1(X0) = sK4
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3439,c_2876])).

cnf(c_6300,plain,
    ( k2_mcart_1(k4_tarski(X0,k1_funct_1(sK6,X0))) = sK4
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3425,c_5543])).

cnf(c_26,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_6301,plain,
    ( k1_funct_1(sK6,X0) = sK4
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6300,c_26])).

cnf(c_6308,plain,
    ( k1_funct_1(sK6,X0) = sK4
    | sK3 = k1_xboole_0
    | sK6 = k1_xboole_0
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3208,c_6301])).

cnf(c_6773,plain,
    ( k1_funct_1(sK6,sK5) = sK4
    | sK3 = k1_xboole_0
    | sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2874,c_6308])).

cnf(c_34,negated_conjecture,
    ( k1_funct_1(sK6,sK5) != sK4 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_6792,plain,
    ( sK3 = k1_xboole_0
    | sK6 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6773,c_34])).

cnf(c_6809,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK5,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6792,c_2874])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_2892,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_7861,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_2892])).

cnf(c_9991,plain,
    ( sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6809,c_7861])).

cnf(c_17,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_2877,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_6058,plain,
    ( k1_relat_1(sK6) = sK3
    | sP1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3183,c_2877])).

cnf(c_10204,plain,
    ( k1_relat_1(k1_xboole_0) = sK3
    | sP1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9991,c_6058])).

cnf(c_120,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_10222,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k1_xboole_0
    | k1_relat_1(k1_xboole_0) = sK3 ),
    inference(demodulation,[status(thm)],[c_9991,c_3183])).

cnf(c_7862,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))
    | k1_relat_1(sK6) = sK3
    | r2_hidden(sK4,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3183,c_2892])).

cnf(c_11411,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))
    | k1_relat_1(k1_xboole_0) = sK3
    | r2_hidden(sK4,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7862,c_9991])).

cnf(c_12412,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) = sK3
    | r2_hidden(sK4,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10222,c_11411])).

cnf(c_12433,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) = sK3
    | r2_hidden(sK4,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_12412])).

cnf(c_7,plain,
    ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_2887,plain,
    ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    | ~ sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9)
    | r2_hidden(X0,X9) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2889,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) != iProver_top
    | sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9) != iProver_top
    | r2_hidden(X0,X9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_7402,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != iProver_top
    | r2_hidden(X7,X8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2887,c_2889])).

cnf(c_11090,plain,
    ( r2_hidden(X0,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2877,c_7402])).

cnf(c_12419,plain,
    ( k1_relat_1(k1_xboole_0) = sK3
    | r2_hidden(sK4,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_10222,c_11090])).

cnf(c_12437,plain,
    ( k1_relat_1(k1_xboole_0) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10204,c_120,c_12433,c_12419])).

cnf(c_10220,plain,
    ( r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9991,c_3425])).

cnf(c_10751,plain,
    ( r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_10220,c_7861])).

cnf(c_12444,plain,
    ( r2_hidden(X0,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12437,c_10751])).

cnf(c_14439,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_2874,c_12444])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:58:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.62/1.04  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.62/1.04  
% 3.62/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.62/1.04  
% 3.62/1.04  ------  iProver source info
% 3.62/1.04  
% 3.62/1.04  git: date: 2020-06-30 10:37:57 +0100
% 3.62/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.62/1.04  git: non_committed_changes: false
% 3.62/1.04  git: last_make_outside_of_git: false
% 3.62/1.04  
% 3.62/1.04  ------ 
% 3.62/1.04  
% 3.62/1.04  ------ Input Options
% 3.62/1.04  
% 3.62/1.04  --out_options                           all
% 3.62/1.04  --tptp_safe_out                         true
% 3.62/1.04  --problem_path                          ""
% 3.62/1.04  --include_path                          ""
% 3.62/1.04  --clausifier                            res/vclausify_rel
% 3.62/1.04  --clausifier_options                    --mode clausify
% 3.62/1.04  --stdin                                 false
% 3.62/1.04  --stats_out                             all
% 3.62/1.04  
% 3.62/1.04  ------ General Options
% 3.62/1.04  
% 3.62/1.04  --fof                                   false
% 3.62/1.04  --time_out_real                         305.
% 3.62/1.04  --time_out_virtual                      -1.
% 3.62/1.04  --symbol_type_check                     false
% 3.62/1.04  --clausify_out                          false
% 3.62/1.04  --sig_cnt_out                           false
% 3.62/1.04  --trig_cnt_out                          false
% 3.62/1.04  --trig_cnt_out_tolerance                1.
% 3.62/1.04  --trig_cnt_out_sk_spl                   false
% 3.62/1.04  --abstr_cl_out                          false
% 3.62/1.04  
% 3.62/1.04  ------ Global Options
% 3.62/1.04  
% 3.62/1.04  --schedule                              default
% 3.62/1.04  --add_important_lit                     false
% 3.62/1.04  --prop_solver_per_cl                    1000
% 3.62/1.04  --min_unsat_core                        false
% 3.62/1.04  --soft_assumptions                      false
% 3.62/1.04  --soft_lemma_size                       3
% 3.62/1.04  --prop_impl_unit_size                   0
% 3.62/1.04  --prop_impl_unit                        []
% 3.62/1.04  --share_sel_clauses                     true
% 3.62/1.04  --reset_solvers                         false
% 3.62/1.04  --bc_imp_inh                            [conj_cone]
% 3.62/1.04  --conj_cone_tolerance                   3.
% 3.62/1.04  --extra_neg_conj                        none
% 3.62/1.04  --large_theory_mode                     true
% 3.62/1.04  --prolific_symb_bound                   200
% 3.62/1.04  --lt_threshold                          2000
% 3.62/1.04  --clause_weak_htbl                      true
% 3.62/1.04  --gc_record_bc_elim                     false
% 3.62/1.04  
% 3.62/1.04  ------ Preprocessing Options
% 3.62/1.04  
% 3.62/1.04  --preprocessing_flag                    true
% 3.62/1.04  --time_out_prep_mult                    0.1
% 3.62/1.04  --splitting_mode                        input
% 3.62/1.04  --splitting_grd                         true
% 3.62/1.04  --splitting_cvd                         false
% 3.62/1.04  --splitting_cvd_svl                     false
% 3.62/1.04  --splitting_nvd                         32
% 3.62/1.04  --sub_typing                            true
% 3.62/1.04  --prep_gs_sim                           true
% 3.62/1.04  --prep_unflatten                        true
% 3.62/1.04  --prep_res_sim                          true
% 3.62/1.04  --prep_upred                            true
% 3.62/1.04  --prep_sem_filter                       exhaustive
% 3.62/1.04  --prep_sem_filter_out                   false
% 3.62/1.04  --pred_elim                             true
% 3.62/1.04  --res_sim_input                         true
% 3.62/1.04  --eq_ax_congr_red                       true
% 3.62/1.04  --pure_diseq_elim                       true
% 3.62/1.04  --brand_transform                       false
% 3.62/1.04  --non_eq_to_eq                          false
% 3.62/1.04  --prep_def_merge                        true
% 3.62/1.04  --prep_def_merge_prop_impl              false
% 3.62/1.04  --prep_def_merge_mbd                    true
% 3.62/1.04  --prep_def_merge_tr_red                 false
% 3.62/1.04  --prep_def_merge_tr_cl                  false
% 3.62/1.04  --smt_preprocessing                     true
% 3.62/1.04  --smt_ac_axioms                         fast
% 3.62/1.04  --preprocessed_out                      false
% 3.62/1.04  --preprocessed_stats                    false
% 3.62/1.04  
% 3.62/1.04  ------ Abstraction refinement Options
% 3.62/1.04  
% 3.62/1.04  --abstr_ref                             []
% 3.62/1.04  --abstr_ref_prep                        false
% 3.62/1.04  --abstr_ref_until_sat                   false
% 3.62/1.04  --abstr_ref_sig_restrict                funpre
% 3.62/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 3.62/1.04  --abstr_ref_under                       []
% 3.62/1.04  
% 3.62/1.04  ------ SAT Options
% 3.62/1.04  
% 3.62/1.04  --sat_mode                              false
% 3.62/1.04  --sat_fm_restart_options                ""
% 3.62/1.04  --sat_gr_def                            false
% 3.62/1.04  --sat_epr_types                         true
% 3.62/1.04  --sat_non_cyclic_types                  false
% 3.62/1.04  --sat_finite_models                     false
% 3.62/1.04  --sat_fm_lemmas                         false
% 3.62/1.04  --sat_fm_prep                           false
% 3.62/1.04  --sat_fm_uc_incr                        true
% 3.62/1.04  --sat_out_model                         small
% 3.62/1.04  --sat_out_clauses                       false
% 3.62/1.04  
% 3.62/1.04  ------ QBF Options
% 3.62/1.04  
% 3.62/1.04  --qbf_mode                              false
% 3.62/1.04  --qbf_elim_univ                         false
% 3.62/1.04  --qbf_dom_inst                          none
% 3.62/1.04  --qbf_dom_pre_inst                      false
% 3.62/1.04  --qbf_sk_in                             false
% 3.62/1.04  --qbf_pred_elim                         true
% 3.62/1.04  --qbf_split                             512
% 3.62/1.04  
% 3.62/1.04  ------ BMC1 Options
% 3.62/1.04  
% 3.62/1.04  --bmc1_incremental                      false
% 3.62/1.04  --bmc1_axioms                           reachable_all
% 3.62/1.04  --bmc1_min_bound                        0
% 3.62/1.04  --bmc1_max_bound                        -1
% 3.62/1.04  --bmc1_max_bound_default                -1
% 3.62/1.04  --bmc1_symbol_reachability              true
% 3.62/1.04  --bmc1_property_lemmas                  false
% 3.62/1.04  --bmc1_k_induction                      false
% 3.62/1.04  --bmc1_non_equiv_states                 false
% 3.62/1.04  --bmc1_deadlock                         false
% 3.62/1.04  --bmc1_ucm                              false
% 3.62/1.04  --bmc1_add_unsat_core                   none
% 3.62/1.04  --bmc1_unsat_core_children              false
% 3.62/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 3.62/1.04  --bmc1_out_stat                         full
% 3.62/1.04  --bmc1_ground_init                      false
% 3.62/1.04  --bmc1_pre_inst_next_state              false
% 3.62/1.04  --bmc1_pre_inst_state                   false
% 3.62/1.04  --bmc1_pre_inst_reach_state             false
% 3.62/1.04  --bmc1_out_unsat_core                   false
% 3.62/1.04  --bmc1_aig_witness_out                  false
% 3.62/1.04  --bmc1_verbose                          false
% 3.62/1.04  --bmc1_dump_clauses_tptp                false
% 3.62/1.04  --bmc1_dump_unsat_core_tptp             false
% 3.62/1.04  --bmc1_dump_file                        -
% 3.62/1.04  --bmc1_ucm_expand_uc_limit              128
% 3.62/1.04  --bmc1_ucm_n_expand_iterations          6
% 3.62/1.04  --bmc1_ucm_extend_mode                  1
% 3.62/1.04  --bmc1_ucm_init_mode                    2
% 3.62/1.04  --bmc1_ucm_cone_mode                    none
% 3.62/1.04  --bmc1_ucm_reduced_relation_type        0
% 3.62/1.04  --bmc1_ucm_relax_model                  4
% 3.62/1.04  --bmc1_ucm_full_tr_after_sat            true
% 3.62/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 3.62/1.04  --bmc1_ucm_layered_model                none
% 3.62/1.04  --bmc1_ucm_max_lemma_size               10
% 3.62/1.04  
% 3.62/1.04  ------ AIG Options
% 3.62/1.04  
% 3.62/1.04  --aig_mode                              false
% 3.62/1.04  
% 3.62/1.04  ------ Instantiation Options
% 3.62/1.04  
% 3.62/1.04  --instantiation_flag                    true
% 3.62/1.04  --inst_sos_flag                         false
% 3.62/1.04  --inst_sos_phase                        true
% 3.62/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.62/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.62/1.04  --inst_lit_sel_side                     num_symb
% 3.62/1.04  --inst_solver_per_active                1400
% 3.62/1.04  --inst_solver_calls_frac                1.
% 3.62/1.04  --inst_passive_queue_type               priority_queues
% 3.62/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.62/1.04  --inst_passive_queues_freq              [25;2]
% 3.62/1.04  --inst_dismatching                      true
% 3.62/1.04  --inst_eager_unprocessed_to_passive     true
% 3.62/1.04  --inst_prop_sim_given                   true
% 3.62/1.04  --inst_prop_sim_new                     false
% 3.62/1.04  --inst_subs_new                         false
% 3.62/1.04  --inst_eq_res_simp                      false
% 3.62/1.04  --inst_subs_given                       false
% 3.62/1.04  --inst_orphan_elimination               true
% 3.62/1.04  --inst_learning_loop_flag               true
% 3.62/1.04  --inst_learning_start                   3000
% 3.62/1.04  --inst_learning_factor                  2
% 3.62/1.04  --inst_start_prop_sim_after_learn       3
% 3.62/1.04  --inst_sel_renew                        solver
% 3.62/1.04  --inst_lit_activity_flag                true
% 3.62/1.04  --inst_restr_to_given                   false
% 3.62/1.04  --inst_activity_threshold               500
% 3.62/1.04  --inst_out_proof                        true
% 3.62/1.04  
% 3.62/1.04  ------ Resolution Options
% 3.62/1.04  
% 3.62/1.04  --resolution_flag                       true
% 3.62/1.04  --res_lit_sel                           adaptive
% 3.62/1.04  --res_lit_sel_side                      none
% 3.62/1.04  --res_ordering                          kbo
% 3.62/1.04  --res_to_prop_solver                    active
% 3.62/1.04  --res_prop_simpl_new                    false
% 3.62/1.04  --res_prop_simpl_given                  true
% 3.62/1.04  --res_passive_queue_type                priority_queues
% 3.62/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.62/1.04  --res_passive_queues_freq               [15;5]
% 3.62/1.04  --res_forward_subs                      full
% 3.62/1.04  --res_backward_subs                     full
% 3.62/1.04  --res_forward_subs_resolution           true
% 3.62/1.04  --res_backward_subs_resolution          true
% 3.62/1.04  --res_orphan_elimination                true
% 3.62/1.04  --res_time_limit                        2.
% 3.62/1.04  --res_out_proof                         true
% 3.62/1.04  
% 3.62/1.04  ------ Superposition Options
% 3.62/1.04  
% 3.62/1.04  --superposition_flag                    true
% 3.62/1.04  --sup_passive_queue_type                priority_queues
% 3.62/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.62/1.04  --sup_passive_queues_freq               [8;1;4]
% 3.62/1.04  --demod_completeness_check              fast
% 3.62/1.04  --demod_use_ground                      true
% 3.62/1.04  --sup_to_prop_solver                    passive
% 3.62/1.04  --sup_prop_simpl_new                    true
% 3.62/1.04  --sup_prop_simpl_given                  true
% 3.62/1.04  --sup_fun_splitting                     false
% 3.62/1.04  --sup_smt_interval                      50000
% 3.62/1.04  
% 3.62/1.04  ------ Superposition Simplification Setup
% 3.62/1.04  
% 3.62/1.04  --sup_indices_passive                   []
% 3.62/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.62/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.62/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.62/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 3.62/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.62/1.04  --sup_full_bw                           [BwDemod]
% 3.62/1.04  --sup_immed_triv                        [TrivRules]
% 3.62/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.62/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.62/1.04  --sup_immed_bw_main                     []
% 3.62/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.62/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 3.62/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.62/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.62/1.04  
% 3.62/1.04  ------ Combination Options
% 3.62/1.04  
% 3.62/1.04  --comb_res_mult                         3
% 3.62/1.04  --comb_sup_mult                         2
% 3.62/1.04  --comb_inst_mult                        10
% 3.62/1.04  
% 3.62/1.04  ------ Debug Options
% 3.62/1.04  
% 3.62/1.04  --dbg_backtrace                         false
% 3.62/1.04  --dbg_dump_prop_clauses                 false
% 3.62/1.04  --dbg_dump_prop_clauses_file            -
% 3.62/1.04  --dbg_out_stat                          false
% 3.62/1.04  ------ Parsing...
% 3.62/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.62/1.04  
% 3.62/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.62/1.04  
% 3.62/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.62/1.04  
% 3.62/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.62/1.04  ------ Proving...
% 3.62/1.04  ------ Problem Properties 
% 3.62/1.04  
% 3.62/1.04  
% 3.62/1.04  clauses                                 33
% 3.62/1.04  conjectures                             2
% 3.62/1.04  EPR                                     12
% 3.62/1.04  Horn                                    28
% 3.62/1.04  unary                                   14
% 3.62/1.04  binary                                  8
% 3.62/1.04  lits                                    70
% 3.62/1.04  lits eq                                 30
% 3.62/1.04  fd_pure                                 0
% 3.62/1.04  fd_pseudo                               0
% 3.62/1.04  fd_cond                                 0
% 3.62/1.04  fd_pseudo_cond                          4
% 3.62/1.04  AC symbols                              0
% 3.62/1.04  
% 3.62/1.04  ------ Schedule dynamic 5 is on 
% 3.62/1.04  
% 3.62/1.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.62/1.04  
% 3.62/1.04  
% 3.62/1.04  ------ 
% 3.62/1.04  Current options:
% 3.62/1.04  ------ 
% 3.62/1.04  
% 3.62/1.04  ------ Input Options
% 3.62/1.04  
% 3.62/1.04  --out_options                           all
% 3.62/1.04  --tptp_safe_out                         true
% 3.62/1.04  --problem_path                          ""
% 3.62/1.04  --include_path                          ""
% 3.62/1.04  --clausifier                            res/vclausify_rel
% 3.62/1.04  --clausifier_options                    --mode clausify
% 3.62/1.04  --stdin                                 false
% 3.62/1.04  --stats_out                             all
% 3.62/1.04  
% 3.62/1.04  ------ General Options
% 3.62/1.04  
% 3.62/1.04  --fof                                   false
% 3.62/1.04  --time_out_real                         305.
% 3.62/1.04  --time_out_virtual                      -1.
% 3.62/1.04  --symbol_type_check                     false
% 3.62/1.04  --clausify_out                          false
% 3.62/1.04  --sig_cnt_out                           false
% 3.62/1.04  --trig_cnt_out                          false
% 3.62/1.04  --trig_cnt_out_tolerance                1.
% 3.62/1.04  --trig_cnt_out_sk_spl                   false
% 3.62/1.04  --abstr_cl_out                          false
% 3.62/1.04  
% 3.62/1.04  ------ Global Options
% 3.62/1.04  
% 3.62/1.04  --schedule                              default
% 3.62/1.04  --add_important_lit                     false
% 3.62/1.04  --prop_solver_per_cl                    1000
% 3.62/1.04  --min_unsat_core                        false
% 3.62/1.04  --soft_assumptions                      false
% 3.62/1.04  --soft_lemma_size                       3
% 3.62/1.04  --prop_impl_unit_size                   0
% 3.62/1.04  --prop_impl_unit                        []
% 3.62/1.04  --share_sel_clauses                     true
% 3.62/1.04  --reset_solvers                         false
% 3.62/1.04  --bc_imp_inh                            [conj_cone]
% 3.62/1.04  --conj_cone_tolerance                   3.
% 3.62/1.04  --extra_neg_conj                        none
% 3.62/1.04  --large_theory_mode                     true
% 3.62/1.04  --prolific_symb_bound                   200
% 3.62/1.04  --lt_threshold                          2000
% 3.62/1.04  --clause_weak_htbl                      true
% 3.62/1.04  --gc_record_bc_elim                     false
% 3.62/1.04  
% 3.62/1.04  ------ Preprocessing Options
% 3.62/1.04  
% 3.62/1.04  --preprocessing_flag                    true
% 3.62/1.04  --time_out_prep_mult                    0.1
% 3.62/1.04  --splitting_mode                        input
% 3.62/1.04  --splitting_grd                         true
% 3.62/1.04  --splitting_cvd                         false
% 3.62/1.04  --splitting_cvd_svl                     false
% 3.62/1.04  --splitting_nvd                         32
% 3.62/1.04  --sub_typing                            true
% 3.62/1.04  --prep_gs_sim                           true
% 3.62/1.04  --prep_unflatten                        true
% 3.62/1.04  --prep_res_sim                          true
% 3.62/1.04  --prep_upred                            true
% 3.62/1.04  --prep_sem_filter                       exhaustive
% 3.62/1.04  --prep_sem_filter_out                   false
% 3.62/1.04  --pred_elim                             true
% 3.62/1.04  --res_sim_input                         true
% 3.62/1.04  --eq_ax_congr_red                       true
% 3.62/1.04  --pure_diseq_elim                       true
% 3.62/1.04  --brand_transform                       false
% 3.62/1.04  --non_eq_to_eq                          false
% 3.62/1.04  --prep_def_merge                        true
% 3.62/1.04  --prep_def_merge_prop_impl              false
% 3.62/1.04  --prep_def_merge_mbd                    true
% 3.62/1.04  --prep_def_merge_tr_red                 false
% 3.62/1.04  --prep_def_merge_tr_cl                  false
% 3.62/1.04  --smt_preprocessing                     true
% 3.62/1.04  --smt_ac_axioms                         fast
% 3.62/1.04  --preprocessed_out                      false
% 3.62/1.04  --preprocessed_stats                    false
% 3.62/1.04  
% 3.62/1.04  ------ Abstraction refinement Options
% 3.62/1.04  
% 3.62/1.04  --abstr_ref                             []
% 3.62/1.04  --abstr_ref_prep                        false
% 3.62/1.04  --abstr_ref_until_sat                   false
% 3.62/1.04  --abstr_ref_sig_restrict                funpre
% 3.62/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 3.62/1.04  --abstr_ref_under                       []
% 3.62/1.04  
% 3.62/1.04  ------ SAT Options
% 3.62/1.04  
% 3.62/1.04  --sat_mode                              false
% 3.62/1.04  --sat_fm_restart_options                ""
% 3.62/1.04  --sat_gr_def                            false
% 3.62/1.04  --sat_epr_types                         true
% 3.62/1.04  --sat_non_cyclic_types                  false
% 3.62/1.04  --sat_finite_models                     false
% 3.62/1.04  --sat_fm_lemmas                         false
% 3.62/1.04  --sat_fm_prep                           false
% 3.62/1.04  --sat_fm_uc_incr                        true
% 3.62/1.04  --sat_out_model                         small
% 3.62/1.04  --sat_out_clauses                       false
% 3.62/1.04  
% 3.62/1.04  ------ QBF Options
% 3.62/1.04  
% 3.62/1.04  --qbf_mode                              false
% 3.62/1.04  --qbf_elim_univ                         false
% 3.62/1.04  --qbf_dom_inst                          none
% 3.62/1.04  --qbf_dom_pre_inst                      false
% 3.62/1.04  --qbf_sk_in                             false
% 3.62/1.04  --qbf_pred_elim                         true
% 3.62/1.04  --qbf_split                             512
% 3.62/1.04  
% 3.62/1.04  ------ BMC1 Options
% 3.62/1.04  
% 3.62/1.04  --bmc1_incremental                      false
% 3.62/1.04  --bmc1_axioms                           reachable_all
% 3.62/1.04  --bmc1_min_bound                        0
% 3.62/1.04  --bmc1_max_bound                        -1
% 3.62/1.04  --bmc1_max_bound_default                -1
% 3.62/1.04  --bmc1_symbol_reachability              true
% 3.62/1.04  --bmc1_property_lemmas                  false
% 3.62/1.04  --bmc1_k_induction                      false
% 3.62/1.04  --bmc1_non_equiv_states                 false
% 3.62/1.04  --bmc1_deadlock                         false
% 3.62/1.04  --bmc1_ucm                              false
% 3.62/1.04  --bmc1_add_unsat_core                   none
% 3.62/1.04  --bmc1_unsat_core_children              false
% 3.62/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 3.62/1.04  --bmc1_out_stat                         full
% 3.62/1.04  --bmc1_ground_init                      false
% 3.62/1.04  --bmc1_pre_inst_next_state              false
% 3.62/1.04  --bmc1_pre_inst_state                   false
% 3.62/1.04  --bmc1_pre_inst_reach_state             false
% 3.62/1.04  --bmc1_out_unsat_core                   false
% 3.62/1.04  --bmc1_aig_witness_out                  false
% 3.62/1.04  --bmc1_verbose                          false
% 3.62/1.04  --bmc1_dump_clauses_tptp                false
% 3.62/1.04  --bmc1_dump_unsat_core_tptp             false
% 3.62/1.04  --bmc1_dump_file                        -
% 3.62/1.04  --bmc1_ucm_expand_uc_limit              128
% 3.62/1.04  --bmc1_ucm_n_expand_iterations          6
% 3.62/1.04  --bmc1_ucm_extend_mode                  1
% 3.62/1.04  --bmc1_ucm_init_mode                    2
% 3.62/1.04  --bmc1_ucm_cone_mode                    none
% 3.62/1.04  --bmc1_ucm_reduced_relation_type        0
% 3.62/1.04  --bmc1_ucm_relax_model                  4
% 3.62/1.04  --bmc1_ucm_full_tr_after_sat            true
% 3.62/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 3.62/1.04  --bmc1_ucm_layered_model                none
% 3.62/1.04  --bmc1_ucm_max_lemma_size               10
% 3.62/1.04  
% 3.62/1.04  ------ AIG Options
% 3.62/1.04  
% 3.62/1.04  --aig_mode                              false
% 3.62/1.04  
% 3.62/1.04  ------ Instantiation Options
% 3.62/1.04  
% 3.62/1.04  --instantiation_flag                    true
% 3.62/1.04  --inst_sos_flag                         false
% 3.62/1.04  --inst_sos_phase                        true
% 3.62/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.62/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.62/1.04  --inst_lit_sel_side                     none
% 3.62/1.04  --inst_solver_per_active                1400
% 3.62/1.04  --inst_solver_calls_frac                1.
% 3.62/1.04  --inst_passive_queue_type               priority_queues
% 3.62/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.62/1.04  --inst_passive_queues_freq              [25;2]
% 3.62/1.04  --inst_dismatching                      true
% 3.62/1.04  --inst_eager_unprocessed_to_passive     true
% 3.62/1.04  --inst_prop_sim_given                   true
% 3.62/1.04  --inst_prop_sim_new                     false
% 3.62/1.04  --inst_subs_new                         false
% 3.62/1.04  --inst_eq_res_simp                      false
% 3.62/1.04  --inst_subs_given                       false
% 3.62/1.04  --inst_orphan_elimination               true
% 3.62/1.04  --inst_learning_loop_flag               true
% 3.62/1.04  --inst_learning_start                   3000
% 3.62/1.04  --inst_learning_factor                  2
% 3.62/1.04  --inst_start_prop_sim_after_learn       3
% 3.62/1.04  --inst_sel_renew                        solver
% 3.62/1.04  --inst_lit_activity_flag                true
% 3.62/1.04  --inst_restr_to_given                   false
% 3.62/1.04  --inst_activity_threshold               500
% 3.62/1.04  --inst_out_proof                        true
% 3.62/1.04  
% 3.62/1.04  ------ Resolution Options
% 3.62/1.04  
% 3.62/1.04  --resolution_flag                       false
% 3.62/1.04  --res_lit_sel                           adaptive
% 3.62/1.04  --res_lit_sel_side                      none
% 3.62/1.04  --res_ordering                          kbo
% 3.62/1.04  --res_to_prop_solver                    active
% 3.62/1.04  --res_prop_simpl_new                    false
% 3.62/1.04  --res_prop_simpl_given                  true
% 3.62/1.04  --res_passive_queue_type                priority_queues
% 3.62/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.62/1.04  --res_passive_queues_freq               [15;5]
% 3.62/1.04  --res_forward_subs                      full
% 3.62/1.04  --res_backward_subs                     full
% 3.62/1.04  --res_forward_subs_resolution           true
% 3.62/1.04  --res_backward_subs_resolution          true
% 3.62/1.04  --res_orphan_elimination                true
% 3.62/1.04  --res_time_limit                        2.
% 3.62/1.04  --res_out_proof                         true
% 3.62/1.04  
% 3.62/1.04  ------ Superposition Options
% 3.62/1.04  
% 3.62/1.04  --superposition_flag                    true
% 3.62/1.04  --sup_passive_queue_type                priority_queues
% 3.62/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.62/1.04  --sup_passive_queues_freq               [8;1;4]
% 3.62/1.04  --demod_completeness_check              fast
% 3.62/1.04  --demod_use_ground                      true
% 3.62/1.04  --sup_to_prop_solver                    passive
% 3.62/1.04  --sup_prop_simpl_new                    true
% 3.62/1.04  --sup_prop_simpl_given                  true
% 3.62/1.04  --sup_fun_splitting                     false
% 3.62/1.04  --sup_smt_interval                      50000
% 3.62/1.04  
% 3.62/1.04  ------ Superposition Simplification Setup
% 3.62/1.04  
% 3.62/1.04  --sup_indices_passive                   []
% 3.62/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.62/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.62/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.62/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 3.62/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.62/1.04  --sup_full_bw                           [BwDemod]
% 3.62/1.04  --sup_immed_triv                        [TrivRules]
% 3.62/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.62/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.62/1.04  --sup_immed_bw_main                     []
% 3.62/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.62/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 3.62/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.62/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.62/1.04  
% 3.62/1.04  ------ Combination Options
% 3.62/1.04  
% 3.62/1.04  --comb_res_mult                         3
% 3.62/1.04  --comb_sup_mult                         2
% 3.62/1.04  --comb_inst_mult                        10
% 3.62/1.04  
% 3.62/1.04  ------ Debug Options
% 3.62/1.04  
% 3.62/1.04  --dbg_backtrace                         false
% 3.62/1.04  --dbg_dump_prop_clauses                 false
% 3.62/1.04  --dbg_dump_prop_clauses_file            -
% 3.62/1.04  --dbg_out_stat                          false
% 3.62/1.04  
% 3.62/1.04  
% 3.62/1.04  
% 3.62/1.04  
% 3.62/1.04  ------ Proving...
% 3.62/1.04  
% 3.62/1.04  
% 3.62/1.04  % SZS status Theorem for theBenchmark.p
% 3.62/1.04  
% 3.62/1.04   Resolution empty clause
% 3.62/1.04  
% 3.62/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 3.62/1.04  
% 3.62/1.04  fof(f19,conjecture,(
% 3.62/1.04    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 3.62/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.04  
% 3.62/1.04  fof(f20,negated_conjecture,(
% 3.62/1.04    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 3.62/1.04    inference(negated_conjecture,[],[f19])).
% 3.62/1.04  
% 3.62/1.04  fof(f30,plain,(
% 3.62/1.04    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 3.62/1.04    inference(ennf_transformation,[],[f20])).
% 3.62/1.04  
% 3.62/1.04  fof(f31,plain,(
% 3.62/1.04    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 3.62/1.04    inference(flattening,[],[f30])).
% 3.62/1.04  
% 3.62/1.04  fof(f47,plain,(
% 3.62/1.04    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (k1_funct_1(sK6,sK5) != sK4 & r2_hidden(sK5,sK3) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4)))) & v1_funct_2(sK6,sK3,k1_tarski(sK4)) & v1_funct_1(sK6))),
% 3.62/1.04    introduced(choice_axiom,[])).
% 3.62/1.04  
% 3.62/1.04  fof(f48,plain,(
% 3.62/1.04    k1_funct_1(sK6,sK5) != sK4 & r2_hidden(sK5,sK3) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4)))) & v1_funct_2(sK6,sK3,k1_tarski(sK4)) & v1_funct_1(sK6)),
% 3.62/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f31,f47])).
% 3.62/1.04  
% 3.62/1.04  fof(f94,plain,(
% 3.62/1.04    r2_hidden(sK5,sK3)),
% 3.62/1.04    inference(cnf_transformation,[],[f48])).
% 3.62/1.04  
% 3.62/1.04  fof(f92,plain,(
% 3.62/1.04    v1_funct_2(sK6,sK3,k1_tarski(sK4))),
% 3.62/1.04    inference(cnf_transformation,[],[f48])).
% 3.62/1.04  
% 3.62/1.04  fof(f3,axiom,(
% 3.62/1.04    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.62/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.04  
% 3.62/1.04  fof(f51,plain,(
% 3.62/1.04    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.62/1.04    inference(cnf_transformation,[],[f3])).
% 3.62/1.04  
% 3.62/1.04  fof(f4,axiom,(
% 3.62/1.04    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.62/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.04  
% 3.62/1.04  fof(f52,plain,(
% 3.62/1.04    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.62/1.04    inference(cnf_transformation,[],[f4])).
% 3.62/1.04  
% 3.62/1.04  fof(f5,axiom,(
% 3.62/1.04    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.62/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.04  
% 3.62/1.04  fof(f53,plain,(
% 3.62/1.04    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.62/1.04    inference(cnf_transformation,[],[f5])).
% 3.62/1.04  
% 3.62/1.04  fof(f6,axiom,(
% 3.62/1.04    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.62/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.04  
% 3.62/1.04  fof(f54,plain,(
% 3.62/1.04    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.62/1.04    inference(cnf_transformation,[],[f6])).
% 3.62/1.04  
% 3.62/1.04  fof(f7,axiom,(
% 3.62/1.04    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.62/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.04  
% 3.62/1.04  fof(f55,plain,(
% 3.62/1.04    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.62/1.04    inference(cnf_transformation,[],[f7])).
% 3.62/1.04  
% 3.62/1.04  fof(f8,axiom,(
% 3.62/1.04    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.62/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.04  
% 3.62/1.04  fof(f56,plain,(
% 3.62/1.04    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.62/1.04    inference(cnf_transformation,[],[f8])).
% 3.62/1.04  
% 3.62/1.04  fof(f9,axiom,(
% 3.62/1.04    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.62/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.04  
% 3.62/1.04  fof(f57,plain,(
% 3.62/1.04    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.62/1.04    inference(cnf_transformation,[],[f9])).
% 3.62/1.04  
% 3.62/1.04  fof(f96,plain,(
% 3.62/1.04    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.62/1.04    inference(definition_unfolding,[],[f56,f57])).
% 3.62/1.04  
% 3.62/1.04  fof(f97,plain,(
% 3.62/1.04    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.62/1.04    inference(definition_unfolding,[],[f55,f96])).
% 3.62/1.04  
% 3.62/1.04  fof(f98,plain,(
% 3.62/1.04    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.62/1.04    inference(definition_unfolding,[],[f54,f97])).
% 3.62/1.04  
% 3.62/1.04  fof(f99,plain,(
% 3.62/1.04    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.62/1.04    inference(definition_unfolding,[],[f53,f98])).
% 3.62/1.04  
% 3.62/1.04  fof(f100,plain,(
% 3.62/1.04    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.62/1.04    inference(definition_unfolding,[],[f52,f99])).
% 3.62/1.04  
% 3.62/1.04  fof(f101,plain,(
% 3.62/1.04    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.62/1.04    inference(definition_unfolding,[],[f51,f100])).
% 3.62/1.04  
% 3.62/1.04  fof(f108,plain,(
% 3.62/1.04    v1_funct_2(sK6,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),
% 3.62/1.04    inference(definition_unfolding,[],[f92,f101])).
% 3.62/1.04  
% 3.62/1.04  fof(f18,axiom,(
% 3.62/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.62/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.04  
% 3.62/1.04  fof(f28,plain,(
% 3.62/1.04    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.62/1.04    inference(ennf_transformation,[],[f18])).
% 3.62/1.04  
% 3.62/1.04  fof(f29,plain,(
% 3.62/1.04    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.62/1.04    inference(flattening,[],[f28])).
% 3.62/1.04  
% 3.62/1.04  fof(f46,plain,(
% 3.62/1.04    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.62/1.04    inference(nnf_transformation,[],[f29])).
% 3.62/1.04  
% 3.62/1.04  fof(f85,plain,(
% 3.62/1.04    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.62/1.04    inference(cnf_transformation,[],[f46])).
% 3.62/1.04  
% 3.62/1.04  fof(f93,plain,(
% 3.62/1.04    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4))))),
% 3.62/1.04    inference(cnf_transformation,[],[f48])).
% 3.62/1.04  
% 3.62/1.04  fof(f107,plain,(
% 3.62/1.04    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))),
% 3.62/1.04    inference(definition_unfolding,[],[f93,f101])).
% 3.62/1.04  
% 3.62/1.04  fof(f15,axiom,(
% 3.62/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.62/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.04  
% 3.62/1.04  fof(f26,plain,(
% 3.62/1.04    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.62/1.04    inference(ennf_transformation,[],[f15])).
% 3.62/1.04  
% 3.62/1.04  fof(f80,plain,(
% 3.62/1.04    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.62/1.04    inference(cnf_transformation,[],[f26])).
% 3.62/1.04  
% 3.62/1.04  fof(f89,plain,(
% 3.62/1.04    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.62/1.04    inference(cnf_transformation,[],[f46])).
% 3.62/1.04  
% 3.62/1.04  fof(f121,plain,(
% 3.62/1.04    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.62/1.04    inference(equality_resolution,[],[f89])).
% 3.62/1.04  
% 3.62/1.04  fof(f13,axiom,(
% 3.62/1.04    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 3.62/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.04  
% 3.62/1.04  fof(f23,plain,(
% 3.62/1.04    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.62/1.04    inference(ennf_transformation,[],[f13])).
% 3.62/1.04  
% 3.62/1.04  fof(f24,plain,(
% 3.62/1.04    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.62/1.04    inference(flattening,[],[f23])).
% 3.62/1.04  
% 3.62/1.04  fof(f44,plain,(
% 3.62/1.04    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.62/1.04    inference(nnf_transformation,[],[f24])).
% 3.62/1.04  
% 3.62/1.04  fof(f45,plain,(
% 3.62/1.04    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.62/1.04    inference(flattening,[],[f44])).
% 3.62/1.04  
% 3.62/1.04  fof(f78,plain,(
% 3.62/1.04    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.62/1.04    inference(cnf_transformation,[],[f45])).
% 3.62/1.04  
% 3.62/1.04  fof(f118,plain,(
% 3.62/1.04    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.62/1.04    inference(equality_resolution,[],[f78])).
% 3.62/1.04  
% 3.62/1.04  fof(f91,plain,(
% 3.62/1.04    v1_funct_1(sK6)),
% 3.62/1.04    inference(cnf_transformation,[],[f48])).
% 3.62/1.04  
% 3.62/1.04  fof(f14,axiom,(
% 3.62/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.62/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.04  
% 3.62/1.04  fof(f25,plain,(
% 3.62/1.04    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.62/1.04    inference(ennf_transformation,[],[f14])).
% 3.62/1.04  
% 3.62/1.04  fof(f79,plain,(
% 3.62/1.04    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.62/1.04    inference(cnf_transformation,[],[f25])).
% 3.62/1.04  
% 3.62/1.04  fof(f12,axiom,(
% 3.62/1.04    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.62/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.04  
% 3.62/1.04  fof(f22,plain,(
% 3.62/1.04    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.62/1.04    inference(ennf_transformation,[],[f12])).
% 3.62/1.04  
% 3.62/1.04  fof(f75,plain,(
% 3.62/1.04    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.62/1.04    inference(cnf_transformation,[],[f22])).
% 3.62/1.04  
% 3.62/1.04  fof(f16,axiom,(
% 3.62/1.04    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) => (k2_mcart_1(X0) = X2 & r2_hidden(k1_mcart_1(X0),X1)))),
% 3.62/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.04  
% 3.62/1.04  fof(f27,plain,(
% 3.62/1.04    ! [X0,X1,X2] : ((k2_mcart_1(X0) = X2 & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))))),
% 3.62/1.04    inference(ennf_transformation,[],[f16])).
% 3.62/1.04  
% 3.62/1.04  fof(f82,plain,(
% 3.62/1.04    ( ! [X2,X0,X1] : (k2_mcart_1(X0) = X2 | ~r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2)))) )),
% 3.62/1.04    inference(cnf_transformation,[],[f27])).
% 3.62/1.04  
% 3.62/1.04  fof(f105,plain,(
% 3.62/1.04    ( ! [X2,X0,X1] : (k2_mcart_1(X0) = X2 | ~r2_hidden(X0,k2_zfmisc_1(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))) )),
% 3.62/1.04    inference(definition_unfolding,[],[f82,f101])).
% 3.62/1.04  
% 3.62/1.04  fof(f17,axiom,(
% 3.62/1.04    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 3.62/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.04  
% 3.62/1.04  fof(f84,plain,(
% 3.62/1.04    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 3.62/1.04    inference(cnf_transformation,[],[f17])).
% 3.62/1.04  
% 3.62/1.04  fof(f95,plain,(
% 3.62/1.04    k1_funct_1(sK6,sK5) != sK4),
% 3.62/1.04    inference(cnf_transformation,[],[f48])).
% 3.62/1.04  
% 3.62/1.04  fof(f2,axiom,(
% 3.62/1.04    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.62/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.04  
% 3.62/1.04  fof(f50,plain,(
% 3.62/1.04    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.62/1.04    inference(cnf_transformation,[],[f2])).
% 3.62/1.04  
% 3.62/1.04  fof(f1,axiom,(
% 3.62/1.04    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.62/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.04  
% 3.62/1.04  fof(f49,plain,(
% 3.62/1.04    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.62/1.04    inference(cnf_transformation,[],[f1])).
% 3.62/1.04  
% 3.62/1.04  fof(f102,plain,(
% 3.62/1.04    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 3.62/1.04    inference(definition_unfolding,[],[f50,f49])).
% 3.62/1.04  
% 3.62/1.04  fof(f10,axiom,(
% 3.62/1.04    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) <=> ~r2_hidden(X0,X1))),
% 3.62/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.04  
% 3.62/1.04  fof(f35,plain,(
% 3.62/1.04    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) | r2_hidden(X0,X1)) & (~r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)))),
% 3.62/1.04    inference(nnf_transformation,[],[f10])).
% 3.62/1.04  
% 3.62/1.04  fof(f58,plain,(
% 3.62/1.04    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)) )),
% 3.62/1.04    inference(cnf_transformation,[],[f35])).
% 3.62/1.04  
% 3.62/1.04  fof(f104,plain,(
% 3.62/1.04    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.62/1.04    inference(definition_unfolding,[],[f58,f49,f101,f101])).
% 3.62/1.04  
% 3.62/1.04  fof(f11,axiom,(
% 3.62/1.04    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> ~(X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)))),
% 3.62/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.04  
% 3.62/1.04  fof(f21,plain,(
% 3.62/1.04    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9)))),
% 3.62/1.04    inference(ennf_transformation,[],[f11])).
% 3.62/1.04  
% 3.62/1.04  fof(f33,plain,(
% 3.62/1.04    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) <=> ! [X9] : (r2_hidden(X9,X8) <=> sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 3.62/1.04    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 3.62/1.04  
% 3.62/1.04  fof(f32,plain,(
% 3.62/1.04    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9))),
% 3.62/1.04    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.62/1.04  
% 3.62/1.04  fof(f34,plain,(
% 3.62/1.04    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8))),
% 3.62/1.04    inference(definition_folding,[],[f21,f33,f32])).
% 3.62/1.04  
% 3.62/1.04  fof(f43,plain,(
% 3.62/1.04    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) & (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8))),
% 3.62/1.04    inference(nnf_transformation,[],[f34])).
% 3.62/1.04  
% 3.62/1.04  fof(f73,plain,(
% 3.62/1.04    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8) )),
% 3.62/1.04    inference(cnf_transformation,[],[f43])).
% 3.62/1.04  
% 3.62/1.04  fof(f117,plain,(
% 3.62/1.04    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))) )),
% 3.62/1.04    inference(equality_resolution,[],[f73])).
% 3.62/1.04  
% 3.62/1.04  fof(f40,plain,(
% 3.62/1.04    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & ((X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9) | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 3.62/1.04    inference(nnf_transformation,[],[f32])).
% 3.62/1.04  
% 3.62/1.04  fof(f41,plain,(
% 3.62/1.04    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 3.62/1.04    inference(flattening,[],[f40])).
% 3.62/1.04  
% 3.62/1.04  fof(f42,plain,(
% 3.62/1.04    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4 & X0 != X5 & X0 != X6 & X0 != X7 & X0 != X8)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | X0 = X8 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 3.62/1.04    inference(rectify,[],[f41])).
% 3.62/1.04  
% 3.62/1.04  fof(f72,plain,(
% 3.62/1.04    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | X0 != X1) )),
% 3.62/1.04    inference(cnf_transformation,[],[f42])).
% 3.62/1.04  
% 3.62/1.04  fof(f109,plain,(
% 3.62/1.04    ( ! [X6,X4,X2,X8,X7,X5,X3,X1] : (sP0(X1,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 3.62/1.04    inference(equality_resolution,[],[f72])).
% 3.62/1.04  
% 3.62/1.04  fof(f36,plain,(
% 3.62/1.04    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8)))) & (! [X9] : ((r2_hidden(X9,X8) | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 3.62/1.04    inference(nnf_transformation,[],[f33])).
% 3.62/1.04  
% 3.62/1.04  fof(f37,plain,(
% 3.62/1.04    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8)))) & (! [X10] : ((r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 3.62/1.04    inference(rectify,[],[f36])).
% 3.62/1.04  
% 3.62/1.04  fof(f38,plain,(
% 3.62/1.04    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] : (? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8))) => ((~sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8))))),
% 3.62/1.04    introduced(choice_axiom,[])).
% 3.62/1.04  
% 3.62/1.04  fof(f39,plain,(
% 3.62/1.04    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ((~sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)))) & (! [X10] : ((r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 3.62/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f38])).
% 3.62/1.04  
% 3.62/1.04  fof(f61,plain,(
% 3.62/1.04    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] : (r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 3.62/1.04    inference(cnf_transformation,[],[f39])).
% 3.62/1.04  
% 3.62/1.04  cnf(c_35,negated_conjecture,
% 3.62/1.04      ( r2_hidden(sK5,sK3) ),
% 3.62/1.04      inference(cnf_transformation,[],[f94]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_2874,plain,
% 3.62/1.04      ( r2_hidden(sK5,sK3) = iProver_top ),
% 3.62/1.04      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_37,negated_conjecture,
% 3.62/1.04      ( v1_funct_2(sK6,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
% 3.62/1.04      inference(cnf_transformation,[],[f108]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_33,plain,
% 3.62/1.04      ( ~ v1_funct_2(X0,X1,X2)
% 3.62/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.62/1.04      | k1_relset_1(X1,X2,X0) = X1
% 3.62/1.04      | k1_xboole_0 = X2 ),
% 3.62/1.04      inference(cnf_transformation,[],[f85]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_36,negated_conjecture,
% 3.62/1.04      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) ),
% 3.62/1.04      inference(cnf_transformation,[],[f107]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_600,plain,
% 3.62/1.04      ( ~ v1_funct_2(X0,X1,X2)
% 3.62/1.04      | k1_relset_1(X1,X2,X0) = X1
% 3.62/1.04      | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 3.62/1.04      | sK6 != X0
% 3.62/1.04      | k1_xboole_0 = X2 ),
% 3.62/1.04      inference(resolution_lifted,[status(thm)],[c_33,c_36]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_601,plain,
% 3.62/1.04      ( ~ v1_funct_2(sK6,X0,X1)
% 3.62/1.04      | k1_relset_1(X0,X1,sK6) = X0
% 3.62/1.04      | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.62/1.04      | k1_xboole_0 = X1 ),
% 3.62/1.04      inference(unflattening,[status(thm)],[c_600]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_964,plain,
% 3.62/1.04      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != X0
% 3.62/1.04      | k1_relset_1(X1,X0,sK6) = X1
% 3.62/1.04      | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0))
% 3.62/1.04      | sK3 != X1
% 3.62/1.04      | sK6 != sK6
% 3.62/1.04      | k1_xboole_0 = X0 ),
% 3.62/1.04      inference(resolution_lifted,[status(thm)],[c_37,c_601]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_965,plain,
% 3.62/1.04      ( k1_relset_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK6) = sK3
% 3.62/1.04      | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))
% 3.62/1.04      | k1_xboole_0 = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 3.62/1.04      inference(unflattening,[status(thm)],[c_964]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_1438,plain,
% 3.62/1.04      ( k1_relset_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK6) = sK3
% 3.62/1.04      | k1_xboole_0 = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 3.62/1.04      inference(equality_resolution_simp,[status(thm)],[c_965]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_23,plain,
% 3.62/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.62/1.04      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.62/1.04      inference(cnf_transformation,[],[f80]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_636,plain,
% 3.62/1.04      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.62/1.04      | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.62/1.04      | sK6 != X2 ),
% 3.62/1.04      inference(resolution_lifted,[status(thm)],[c_23,c_36]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_637,plain,
% 3.62/1.04      ( k1_relset_1(X0,X1,sK6) = k1_relat_1(sK6)
% 3.62/1.04      | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 3.62/1.04      inference(unflattening,[status(thm)],[c_636]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_3100,plain,
% 3.62/1.04      ( k1_relset_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK6) = k1_relat_1(sK6) ),
% 3.62/1.04      inference(equality_resolution,[status(thm)],[c_637]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_3183,plain,
% 3.62/1.04      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k1_xboole_0
% 3.62/1.04      | k1_relat_1(sK6) = sK3 ),
% 3.62/1.04      inference(demodulation,[status(thm)],[c_1438,c_3100]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_29,plain,
% 3.62/1.04      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 3.62/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.62/1.04      | k1_xboole_0 = X1
% 3.62/1.04      | k1_xboole_0 = X0 ),
% 3.62/1.04      inference(cnf_transformation,[],[f121]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_674,plain,
% 3.62/1.04      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 3.62/1.04      | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))
% 3.62/1.04      | sK6 != X0
% 3.62/1.04      | k1_xboole_0 = X0
% 3.62/1.04      | k1_xboole_0 = X1 ),
% 3.62/1.04      inference(resolution_lifted,[status(thm)],[c_29,c_36]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_675,plain,
% 3.62/1.04      ( ~ v1_funct_2(sK6,X0,k1_xboole_0)
% 3.62/1.04      | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))
% 3.62/1.04      | k1_xboole_0 = X0
% 3.62/1.04      | k1_xboole_0 = sK6 ),
% 3.62/1.04      inference(unflattening,[status(thm)],[c_674]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_975,plain,
% 3.62/1.04      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k1_xboole_0
% 3.62/1.04      | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))
% 3.62/1.04      | sK3 != X0
% 3.62/1.04      | sK6 != sK6
% 3.62/1.04      | sK6 = k1_xboole_0
% 3.62/1.04      | k1_xboole_0 = X0 ),
% 3.62/1.04      inference(resolution_lifted,[status(thm)],[c_37,c_675]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_976,plain,
% 3.62/1.04      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k1_xboole_0
% 3.62/1.04      | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))
% 3.62/1.04      | sK6 = k1_xboole_0
% 3.62/1.04      | k1_xboole_0 = sK3 ),
% 3.62/1.04      inference(unflattening,[status(thm)],[c_975]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_3187,plain,
% 3.62/1.04      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k1_xboole_0
% 3.62/1.04      | k1_relat_1(sK6) = sK3
% 3.62/1.04      | sK3 = k1_xboole_0
% 3.62/1.04      | sK6 = k1_xboole_0 ),
% 3.62/1.04      inference(superposition,[status(thm)],[c_3183,c_976]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_3208,plain,
% 3.62/1.04      ( k1_relat_1(sK6) = sK3 | sK3 = k1_xboole_0 | sK6 = k1_xboole_0 ),
% 3.62/1.04      inference(forward_subsumption_resolution,[status(thm)],[c_3187,c_3183]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_19,plain,
% 3.62/1.04      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.62/1.04      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 3.62/1.04      | ~ v1_relat_1(X1)
% 3.62/1.04      | ~ v1_funct_1(X1) ),
% 3.62/1.04      inference(cnf_transformation,[],[f118]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_38,negated_conjecture,
% 3.62/1.04      ( v1_funct_1(sK6) ),
% 3.62/1.04      inference(cnf_transformation,[],[f91]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_504,plain,
% 3.62/1.04      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.62/1.04      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 3.62/1.04      | ~ v1_relat_1(X1)
% 3.62/1.04      | sK6 != X1 ),
% 3.62/1.04      inference(resolution_lifted,[status(thm)],[c_19,c_38]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_505,plain,
% 3.62/1.04      ( ~ r2_hidden(X0,k1_relat_1(sK6))
% 3.62/1.04      | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6)
% 3.62/1.04      | ~ v1_relat_1(sK6) ),
% 3.62/1.04      inference(unflattening,[status(thm)],[c_504]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_2871,plain,
% 3.62/1.04      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 3.62/1.04      | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top
% 3.62/1.04      | v1_relat_1(sK6) != iProver_top ),
% 3.62/1.04      inference(predicate_to_equality,[status(thm)],[c_505]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_506,plain,
% 3.62/1.04      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 3.62/1.04      | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top
% 3.62/1.04      | v1_relat_1(sK6) != iProver_top ),
% 3.62/1.04      inference(predicate_to_equality,[status(thm)],[c_505]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_2224,plain,( X0 = X0 ),theory(equality) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_3091,plain,
% 3.62/1.04      ( k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) ),
% 3.62/1.04      inference(instantiation,[status(thm)],[c_2224]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_22,plain,
% 3.62/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.62/1.04      inference(cnf_transformation,[],[f79]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_645,plain,
% 3.62/1.04      ( v1_relat_1(X0)
% 3.62/1.04      | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 3.62/1.04      | sK6 != X0 ),
% 3.62/1.04      inference(resolution_lifted,[status(thm)],[c_22,c_36]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_646,plain,
% 3.62/1.04      ( v1_relat_1(sK6)
% 3.62/1.04      | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 3.62/1.04      inference(unflattening,[status(thm)],[c_645]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_3093,plain,
% 3.62/1.04      ( v1_relat_1(sK6)
% 3.62/1.04      | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) ),
% 3.62/1.04      inference(instantiation,[status(thm)],[c_646]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_3094,plain,
% 3.62/1.04      ( k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))
% 3.62/1.04      | v1_relat_1(sK6) = iProver_top ),
% 3.62/1.04      inference(predicate_to_equality,[status(thm)],[c_3093]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_3424,plain,
% 3.62/1.04      ( r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top
% 3.62/1.04      | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
% 3.62/1.04      inference(global_propositional_subsumption,
% 3.62/1.04                [status(thm)],
% 3.62/1.04                [c_2871,c_506,c_3091,c_3094]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_3425,plain,
% 3.62/1.04      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 3.62/1.04      | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top ),
% 3.62/1.04      inference(renaming,[status(thm)],[c_3424]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_18,plain,
% 3.62/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.62/1.04      | ~ r2_hidden(X2,X0)
% 3.62/1.04      | r2_hidden(X2,X1) ),
% 3.62/1.04      inference(cnf_transformation,[],[f75]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_585,plain,
% 3.62/1.04      ( ~ r2_hidden(X0,X1)
% 3.62/1.04      | r2_hidden(X0,X2)
% 3.62/1.04      | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(X2)
% 3.62/1.04      | sK6 != X1 ),
% 3.62/1.04      inference(resolution_lifted,[status(thm)],[c_18,c_36]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_586,plain,
% 3.62/1.04      ( r2_hidden(X0,X1)
% 3.62/1.04      | ~ r2_hidden(X0,sK6)
% 3.62/1.04      | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(X1) ),
% 3.62/1.04      inference(unflattening,[status(thm)],[c_585]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_2870,plain,
% 3.62/1.04      ( k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(X0)
% 3.62/1.04      | r2_hidden(X1,X0) = iProver_top
% 3.62/1.04      | r2_hidden(X1,sK6) != iProver_top ),
% 3.62/1.04      inference(predicate_to_equality,[status(thm)],[c_586]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_3439,plain,
% 3.62/1.04      ( r2_hidden(X0,k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = iProver_top
% 3.62/1.04      | r2_hidden(X0,sK6) != iProver_top ),
% 3.62/1.04      inference(equality_resolution,[status(thm)],[c_2870]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_24,plain,
% 3.62/1.04      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))
% 3.62/1.04      | k2_mcart_1(X0) = X2 ),
% 3.62/1.04      inference(cnf_transformation,[],[f105]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_2876,plain,
% 3.62/1.04      ( k2_mcart_1(X0) = X1
% 3.62/1.04      | r2_hidden(X0,k2_zfmisc_1(X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) != iProver_top ),
% 3.62/1.04      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_5543,plain,
% 3.62/1.04      ( k2_mcart_1(X0) = sK4 | r2_hidden(X0,sK6) != iProver_top ),
% 3.62/1.04      inference(superposition,[status(thm)],[c_3439,c_2876]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_6300,plain,
% 3.62/1.04      ( k2_mcart_1(k4_tarski(X0,k1_funct_1(sK6,X0))) = sK4
% 3.62/1.04      | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
% 3.62/1.04      inference(superposition,[status(thm)],[c_3425,c_5543]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_26,plain,
% 3.62/1.04      ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
% 3.62/1.04      inference(cnf_transformation,[],[f84]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_6301,plain,
% 3.62/1.04      ( k1_funct_1(sK6,X0) = sK4
% 3.62/1.04      | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
% 3.62/1.04      inference(demodulation,[status(thm)],[c_6300,c_26]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_6308,plain,
% 3.62/1.04      ( k1_funct_1(sK6,X0) = sK4
% 3.62/1.04      | sK3 = k1_xboole_0
% 3.62/1.04      | sK6 = k1_xboole_0
% 3.62/1.04      | r2_hidden(X0,sK3) != iProver_top ),
% 3.62/1.04      inference(superposition,[status(thm)],[c_3208,c_6301]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_6773,plain,
% 3.62/1.04      ( k1_funct_1(sK6,sK5) = sK4 | sK3 = k1_xboole_0 | sK6 = k1_xboole_0 ),
% 3.62/1.04      inference(superposition,[status(thm)],[c_2874,c_6308]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_34,negated_conjecture,
% 3.62/1.04      ( k1_funct_1(sK6,sK5) != sK4 ),
% 3.62/1.04      inference(cnf_transformation,[],[f95]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_6792,plain,
% 3.62/1.04      ( sK3 = k1_xboole_0 | sK6 = k1_xboole_0 ),
% 3.62/1.04      inference(global_propositional_subsumption,[status(thm)],[c_6773,c_34]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_6809,plain,
% 3.62/1.04      ( sK6 = k1_xboole_0 | r2_hidden(sK5,k1_xboole_0) = iProver_top ),
% 3.62/1.04      inference(superposition,[status(thm)],[c_6792,c_2874]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_0,plain,
% 3.62/1.04      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 3.62/1.04      inference(cnf_transformation,[],[f102]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_2,plain,
% 3.62/1.04      ( ~ r2_hidden(X0,X1)
% 3.62/1.04      | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 3.62/1.04      inference(cnf_transformation,[],[f104]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_2892,plain,
% 3.62/1.04      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
% 3.62/1.04      | r2_hidden(X0,X1) != iProver_top ),
% 3.62/1.04      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_7861,plain,
% 3.62/1.04      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.62/1.04      inference(superposition,[status(thm)],[c_0,c_2892]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_9991,plain,
% 3.62/1.04      ( sK6 = k1_xboole_0 ),
% 3.62/1.04      inference(superposition,[status(thm)],[c_6809,c_7861]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_17,plain,
% 3.62/1.04      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
% 3.62/1.04      inference(cnf_transformation,[],[f117]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_2877,plain,
% 3.62/1.04      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) = iProver_top ),
% 3.62/1.04      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_6058,plain,
% 3.62/1.04      ( k1_relat_1(sK6) = sK3
% 3.62/1.04      | sP1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4,k1_xboole_0) = iProver_top ),
% 3.62/1.04      inference(superposition,[status(thm)],[c_3183,c_2877]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_10204,plain,
% 3.62/1.04      ( k1_relat_1(k1_xboole_0) = sK3
% 3.62/1.04      | sP1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4,k1_xboole_0) = iProver_top ),
% 3.62/1.04      inference(demodulation,[status(thm)],[c_9991,c_6058]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_120,plain,
% 3.62/1.04      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
% 3.62/1.04      inference(instantiation,[status(thm)],[c_0]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_10222,plain,
% 3.62/1.04      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k1_xboole_0
% 3.62/1.04      | k1_relat_1(k1_xboole_0) = sK3 ),
% 3.62/1.04      inference(demodulation,[status(thm)],[c_9991,c_3183]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_7862,plain,
% 3.62/1.04      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))
% 3.62/1.04      | k1_relat_1(sK6) = sK3
% 3.62/1.04      | r2_hidden(sK4,X0) != iProver_top ),
% 3.62/1.04      inference(superposition,[status(thm)],[c_3183,c_2892]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_11411,plain,
% 3.62/1.04      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))
% 3.62/1.04      | k1_relat_1(k1_xboole_0) = sK3
% 3.62/1.04      | r2_hidden(sK4,X0) != iProver_top ),
% 3.62/1.04      inference(light_normalisation,[status(thm)],[c_7862,c_9991]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_12412,plain,
% 3.62/1.04      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) != k1_xboole_0
% 3.62/1.04      | k1_relat_1(k1_xboole_0) = sK3
% 3.62/1.04      | r2_hidden(sK4,X0) != iProver_top ),
% 3.62/1.04      inference(superposition,[status(thm)],[c_10222,c_11411]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_12433,plain,
% 3.62/1.04      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) != k1_xboole_0
% 3.62/1.04      | k1_relat_1(k1_xboole_0) = sK3
% 3.62/1.04      | r2_hidden(sK4,k1_xboole_0) != iProver_top ),
% 3.62/1.04      inference(instantiation,[status(thm)],[c_12412]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_7,plain,
% 3.62/1.04      ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7) ),
% 3.62/1.04      inference(cnf_transformation,[],[f109]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_2887,plain,
% 3.62/1.04      ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7) = iProver_top ),
% 3.62/1.04      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_5,plain,
% 3.62/1.04      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
% 3.62/1.04      | ~ sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9)
% 3.62/1.04      | r2_hidden(X0,X9) ),
% 3.62/1.04      inference(cnf_transformation,[],[f61]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_2889,plain,
% 3.62/1.04      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) != iProver_top
% 3.62/1.04      | sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9) != iProver_top
% 3.62/1.04      | r2_hidden(X0,X9) = iProver_top ),
% 3.62/1.04      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_7402,plain,
% 3.62/1.04      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != iProver_top
% 3.62/1.04      | r2_hidden(X7,X8) = iProver_top ),
% 3.62/1.04      inference(superposition,[status(thm)],[c_2887,c_2889]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_11090,plain,
% 3.62/1.04      ( r2_hidden(X0,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X0)) = iProver_top ),
% 3.62/1.04      inference(superposition,[status(thm)],[c_2877,c_7402]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_12419,plain,
% 3.62/1.04      ( k1_relat_1(k1_xboole_0) = sK3
% 3.62/1.04      | r2_hidden(sK4,k1_xboole_0) = iProver_top ),
% 3.62/1.04      inference(superposition,[status(thm)],[c_10222,c_11090]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_12437,plain,
% 3.62/1.04      ( k1_relat_1(k1_xboole_0) = sK3 ),
% 3.62/1.04      inference(global_propositional_subsumption,
% 3.62/1.04                [status(thm)],
% 3.62/1.04                [c_10204,c_120,c_12433,c_12419]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_10220,plain,
% 3.62/1.04      ( r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top
% 3.62/1.04      | r2_hidden(k4_tarski(X0,k1_funct_1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top ),
% 3.62/1.04      inference(demodulation,[status(thm)],[c_9991,c_3425]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_10751,plain,
% 3.62/1.04      ( r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top ),
% 3.62/1.04      inference(forward_subsumption_resolution,[status(thm)],[c_10220,c_7861]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_12444,plain,
% 3.62/1.04      ( r2_hidden(X0,sK3) != iProver_top ),
% 3.62/1.04      inference(demodulation,[status(thm)],[c_12437,c_10751]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_14439,plain,
% 3.62/1.04      ( $false ),
% 3.62/1.04      inference(superposition,[status(thm)],[c_2874,c_12444]) ).
% 3.62/1.04  
% 3.62/1.04  
% 3.62/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 3.62/1.04  
% 3.62/1.04  ------                               Statistics
% 3.62/1.04  
% 3.62/1.04  ------ General
% 3.62/1.04  
% 3.62/1.04  abstr_ref_over_cycles:                  0
% 3.62/1.04  abstr_ref_under_cycles:                 0
% 3.62/1.04  gc_basic_clause_elim:                   0
% 3.62/1.04  forced_gc_time:                         0
% 3.62/1.04  parsing_time:                           0.008
% 3.62/1.04  unif_index_cands_time:                  0.
% 3.62/1.04  unif_index_add_time:                    0.
% 3.62/1.04  orderings_time:                         0.
% 3.62/1.04  out_proof_time:                         0.01
% 3.62/1.04  total_time:                             0.507
% 3.62/1.04  num_of_symbols:                         55
% 3.62/1.04  num_of_terms:                           16546
% 3.62/1.04  
% 3.62/1.04  ------ Preprocessing
% 3.62/1.04  
% 3.62/1.04  num_of_splits:                          0
% 3.62/1.04  num_of_split_atoms:                     0
% 3.62/1.04  num_of_reused_defs:                     0
% 3.62/1.04  num_eq_ax_congr_red:                    82
% 3.62/1.04  num_of_sem_filtered_clauses:            1
% 3.62/1.04  num_of_subtypes:                        0
% 3.62/1.04  monotx_restored_types:                  0
% 3.62/1.04  sat_num_of_epr_types:                   0
% 3.62/1.04  sat_num_of_non_cyclic_types:            0
% 3.62/1.04  sat_guarded_non_collapsed_types:        0
% 3.62/1.04  num_pure_diseq_elim:                    0
% 3.62/1.04  simp_replaced_by:                       0
% 3.62/1.04  res_preprocessed:                       173
% 3.62/1.04  prep_upred:                             0
% 3.62/1.04  prep_unflattend:                        627
% 3.62/1.04  smt_new_axioms:                         0
% 3.62/1.04  pred_elim_cands:                        4
% 3.62/1.04  pred_elim:                              3
% 3.62/1.04  pred_elim_cl:                           6
% 3.62/1.04  pred_elim_cycles:                       10
% 3.62/1.04  merged_defs:                            8
% 3.62/1.04  merged_defs_ncl:                        0
% 3.62/1.04  bin_hyper_res:                          8
% 3.62/1.04  prep_cycles:                            4
% 3.62/1.04  pred_elim_time:                         0.036
% 3.62/1.04  splitting_time:                         0.
% 3.62/1.04  sem_filter_time:                        0.
% 3.62/1.04  monotx_time:                            0.
% 3.62/1.04  subtype_inf_time:                       0.
% 3.62/1.04  
% 3.62/1.04  ------ Problem properties
% 3.62/1.04  
% 3.62/1.04  clauses:                                33
% 3.62/1.04  conjectures:                            2
% 3.62/1.04  epr:                                    12
% 3.62/1.04  horn:                                   28
% 3.62/1.04  ground:                                 5
% 3.62/1.04  unary:                                  14
% 3.62/1.04  binary:                                 8
% 3.62/1.04  lits:                                   70
% 3.62/1.04  lits_eq:                                30
% 3.62/1.04  fd_pure:                                0
% 3.62/1.04  fd_pseudo:                              0
% 3.62/1.04  fd_cond:                                0
% 3.62/1.04  fd_pseudo_cond:                         4
% 3.62/1.04  ac_symbols:                             0
% 3.62/1.04  
% 3.62/1.04  ------ Propositional Solver
% 3.62/1.04  
% 3.62/1.04  prop_solver_calls:                      28
% 3.62/1.04  prop_fast_solver_calls:                 1340
% 3.62/1.04  smt_solver_calls:                       0
% 3.62/1.04  smt_fast_solver_calls:                  0
% 3.62/1.04  prop_num_of_clauses:                    4681
% 3.62/1.04  prop_preprocess_simplified:             14282
% 3.62/1.04  prop_fo_subsumed:                       24
% 3.62/1.04  prop_solver_time:                       0.
% 3.62/1.04  smt_solver_time:                        0.
% 3.62/1.04  smt_fast_solver_time:                   0.
% 3.62/1.04  prop_fast_solver_time:                  0.
% 3.62/1.04  prop_unsat_core_time:                   0.
% 3.62/1.04  
% 3.62/1.04  ------ QBF
% 3.62/1.04  
% 3.62/1.04  qbf_q_res:                              0
% 3.62/1.04  qbf_num_tautologies:                    0
% 3.62/1.04  qbf_prep_cycles:                        0
% 3.62/1.04  
% 3.62/1.04  ------ BMC1
% 3.62/1.04  
% 3.62/1.04  bmc1_current_bound:                     -1
% 3.62/1.04  bmc1_last_solved_bound:                 -1
% 3.62/1.04  bmc1_unsat_core_size:                   -1
% 3.62/1.04  bmc1_unsat_core_parents_size:           -1
% 3.62/1.04  bmc1_merge_next_fun:                    0
% 3.62/1.04  bmc1_unsat_core_clauses_time:           0.
% 3.62/1.04  
% 3.62/1.04  ------ Instantiation
% 3.62/1.04  
% 3.62/1.04  inst_num_of_clauses:                    1420
% 3.62/1.04  inst_num_in_passive:                    440
% 3.62/1.04  inst_num_in_active:                     415
% 3.62/1.04  inst_num_in_unprocessed:                565
% 3.62/1.04  inst_num_of_loops:                      460
% 3.62/1.04  inst_num_of_learning_restarts:          0
% 3.62/1.04  inst_num_moves_active_passive:          44
% 3.62/1.04  inst_lit_activity:                      0
% 3.62/1.04  inst_lit_activity_moves:                0
% 3.62/1.04  inst_num_tautologies:                   0
% 3.62/1.04  inst_num_prop_implied:                  0
% 3.62/1.04  inst_num_existing_simplified:           0
% 3.62/1.04  inst_num_eq_res_simplified:             0
% 3.62/1.04  inst_num_child_elim:                    0
% 3.62/1.04  inst_num_of_dismatching_blockings:      370
% 3.62/1.04  inst_num_of_non_proper_insts:           962
% 3.62/1.04  inst_num_of_duplicates:                 0
% 3.62/1.04  inst_inst_num_from_inst_to_res:         0
% 3.62/1.04  inst_dismatching_checking_time:         0.
% 3.62/1.04  
% 3.62/1.04  ------ Resolution
% 3.62/1.04  
% 3.62/1.04  res_num_of_clauses:                     0
% 3.62/1.04  res_num_in_passive:                     0
% 3.62/1.04  res_num_in_active:                      0
% 3.62/1.04  res_num_of_loops:                       177
% 3.62/1.04  res_forward_subset_subsumed:            216
% 3.62/1.04  res_backward_subset_subsumed:           0
% 3.62/1.04  res_forward_subsumed:                   0
% 3.62/1.04  res_backward_subsumed:                  0
% 3.62/1.04  res_forward_subsumption_resolution:     0
% 3.62/1.04  res_backward_subsumption_resolution:    0
% 3.62/1.04  res_clause_to_clause_subsumption:       1121
% 3.62/1.04  res_orphan_elimination:                 0
% 3.62/1.04  res_tautology_del:                      196
% 3.62/1.04  res_num_eq_res_simplified:              1
% 3.62/1.04  res_num_sel_changes:                    0
% 3.62/1.04  res_moves_from_active_to_pass:          0
% 3.62/1.04  
% 3.62/1.04  ------ Superposition
% 3.62/1.04  
% 3.62/1.04  sup_time_total:                         0.
% 3.62/1.04  sup_time_generating:                    0.
% 3.62/1.04  sup_time_sim_full:                      0.
% 3.62/1.04  sup_time_sim_immed:                     0.
% 3.62/1.04  
% 3.62/1.04  sup_num_of_clauses:                     75
% 3.62/1.04  sup_num_in_active:                      47
% 3.62/1.04  sup_num_in_passive:                     28
% 3.62/1.04  sup_num_of_loops:                       91
% 3.62/1.04  sup_fw_superposition:                   79
% 3.62/1.04  sup_bw_superposition:                   64
% 3.62/1.04  sup_immediate_simplified:               36
% 3.62/1.04  sup_given_eliminated:                   0
% 3.62/1.04  comparisons_done:                       0
% 3.62/1.04  comparisons_avoided:                    24
% 3.62/1.04  
% 3.62/1.04  ------ Simplifications
% 3.62/1.04  
% 3.62/1.04  
% 3.62/1.04  sim_fw_subset_subsumed:                 23
% 3.62/1.04  sim_bw_subset_subsumed:                 8
% 3.62/1.04  sim_fw_subsumed:                        11
% 3.62/1.04  sim_bw_subsumed:                        0
% 3.62/1.04  sim_fw_subsumption_res:                 3
% 3.62/1.04  sim_bw_subsumption_res:                 0
% 3.62/1.04  sim_tautology_del:                      2
% 3.62/1.04  sim_eq_tautology_del:                   20
% 3.62/1.04  sim_eq_res_simp:                        0
% 3.62/1.04  sim_fw_demodulated:                     4
% 3.62/1.04  sim_bw_demodulated:                     42
% 3.62/1.04  sim_light_normalised:                   5
% 3.62/1.04  sim_joinable_taut:                      0
% 3.62/1.04  sim_joinable_simp:                      0
% 3.62/1.04  sim_ac_normalised:                      0
% 3.62/1.04  sim_smt_subsumption:                    0
% 3.62/1.04  
%------------------------------------------------------------------------------
