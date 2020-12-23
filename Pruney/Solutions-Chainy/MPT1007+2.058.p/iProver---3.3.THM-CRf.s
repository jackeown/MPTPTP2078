%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:04:53 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 912 expanded)
%              Number of clauses        :   41 (  97 expanded)
%              Number of leaves         :   22 ( 263 expanded)
%              Depth                    :   23
%              Number of atoms          :  265 (1982 expanded)
%              Number of equality atoms :  146 (1042 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f17,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f85,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f121,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f85,f120])).

fof(f122,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f69,f121])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f12])).

fof(f116,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f77,f78])).

fof(f117,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f76,f116])).

fof(f118,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f75,f117])).

fof(f119,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f74,f118])).

fof(f120,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f73,f119])).

fof(f124,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f72,f120])).

fof(f130,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f82,f122,f124])).

fof(f31,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f31])).

fof(f52,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f53,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f52])).

fof(f65,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( ~ r2_hidden(k1_funct_1(sK4,sK2),sK3)
      & k1_xboole_0 != sK3
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))
      & v1_funct_2(sK4,k1_tarski(sK2),sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,
    ( ~ r2_hidden(k1_funct_1(sK4,sK2),sK3)
    & k1_xboole_0 != sK3
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))
    & v1_funct_2(sK4,k1_tarski(sK2),sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f53,f65])).

fof(f113,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) ),
    inference(cnf_transformation,[],[f66])).

fof(f143,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) ),
    inference(definition_unfolding,[],[f113,f124])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f29,axiom,(
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

fof(f48,plain,(
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
    inference(ennf_transformation,[],[f29])).

fof(f49,plain,(
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
    inference(flattening,[],[f48])).

fof(f64,plain,(
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
    inference(nnf_transformation,[],[f49])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | o_0_0_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_unfolding,[],[f104,f67])).

fof(f112,plain,(
    v1_funct_2(sK4,k1_tarski(sK2),sK3) ),
    inference(cnf_transformation,[],[f66])).

fof(f144,plain,(
    v1_funct_2(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) ),
    inference(definition_unfolding,[],[f112,f124])).

fof(f114,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f66])).

fof(f142,plain,(
    o_0_0_xboole_0 != sK3 ),
    inference(definition_unfolding,[],[f114,f67])).

fof(f30,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f50])).

fof(f110,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f141,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | o_0_0_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(definition_unfolding,[],[f110,f67])).

fof(f111,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f66])).

fof(f115,plain,(
    ~ r2_hidden(k1_funct_1(sK4,sK2),sK3) ),
    inference(cnf_transformation,[],[f66])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X0,X1] : k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f129,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f80,f121,f124,f120,f124])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f128,plain,(
    ! [X0] : o_0_0_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(definition_unfolding,[],[f71,f67])).

fof(f24,axiom,(
    ! [X0] : k1_ordinal1(X0) != X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f99,plain,(
    ! [X0] : k1_ordinal1(X0) != X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f23,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f98,plain,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f23])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f123,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f79,f120])).

fof(f125,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k1_ordinal1(X0) ),
    inference(definition_unfolding,[],[f98,f123,f124])).

fof(f134,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) != X0 ),
    inference(definition_unfolding,[],[f99,f125])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f127,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,o_0_0_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f70,f123,f67])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = X1 ),
    inference(cnf_transformation,[],[f130])).

cnf(c_2412,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) = X0
    | r2_hidden(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) ),
    inference(cnf_transformation,[],[f143])).

cnf(c_2403,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_2406,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3935,plain,
    ( k1_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_2403,c_2406])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | o_0_0_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f140])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) ),
    inference(cnf_transformation,[],[f144])).

cnf(c_1156,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != X1
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X2
    | sK4 != X0
    | o_0_0_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_35])).

cnf(c_1157,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))
    | k1_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | o_0_0_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_1156])).

cnf(c_33,negated_conjecture,
    ( o_0_0_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f142])).

cnf(c_1159,plain,
    ( k1_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1157,c_34,c_33])).

cnf(c_4226,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_3935,c_1159])).

cnf(c_31,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | o_0_0_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f141])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_605,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | sK4 != X0
    | o_0_0_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_36])).

cnf(c_606,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(k1_funct_1(sK4,X2),X1)
    | o_0_0_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_605])).

cnf(c_1183,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(k1_funct_1(sK4,X2),X1)
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != X0
    | sK3 != X1
    | sK4 != sK4
    | o_0_0_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_35,c_606])).

cnf(c_1184,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))
    | ~ r2_hidden(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | r2_hidden(k1_funct_1(sK4,X0),sK3)
    | o_0_0_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_1183])).

cnf(c_1188,plain,
    ( r2_hidden(k1_funct_1(sK4,X0),sK3)
    | ~ r2_hidden(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1184,c_34,c_33])).

cnf(c_1189,plain,
    ( ~ r2_hidden(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | r2_hidden(k1_funct_1(sK4,X0),sK3) ),
    inference(renaming,[status(thm)],[c_1188])).

cnf(c_2388,plain,
    ( r2_hidden(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1189])).

cnf(c_4232,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4226,c_2388])).

cnf(c_32,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(sK4,sK2),sK3) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_2404,plain,
    ( r2_hidden(k1_funct_1(sK4,sK2),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_5112,plain,
    ( r2_hidden(sK2,k1_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4232,c_2404])).

cnf(c_5116,plain,
    ( k5_xboole_0(k1_relat_1(sK4),k1_setfam_1(k6_enumset1(k1_relat_1(sK4),k1_relat_1(sK4),k1_relat_1(sK4),k1_relat_1(sK4),k1_relat_1(sK4),k1_relat_1(sK4),k1_relat_1(sK4),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_2412,c_5112])).

cnf(c_5121,plain,
    ( k5_xboole_0(k1_relat_1(sK4),k1_setfam_1(k6_enumset1(k1_relat_1(sK4),k1_relat_1(sK4),k1_relat_1(sK4),k1_relat_1(sK4),k1_relat_1(sK4),k1_relat_1(sK4),k1_relat_1(sK4),k1_relat_1(sK4)))) = k1_relat_1(sK4) ),
    inference(light_normalisation,[status(thm)],[c_5116,c_4226])).

cnf(c_3,plain,
    ( k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_4263,plain,
    ( k1_setfam_1(k6_enumset1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_relat_1(sK4))) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(superposition,[status(thm)],[c_4226,c_3])).

cnf(c_4264,plain,
    ( k1_setfam_1(k6_enumset1(k1_relat_1(sK4),k1_relat_1(sK4),k1_relat_1(sK4),k1_relat_1(sK4),k1_relat_1(sK4),k1_relat_1(sK4),k1_relat_1(sK4),k1_relat_1(sK4))) = k1_relat_1(sK4) ),
    inference(light_normalisation,[status(thm)],[c_4263,c_4226])).

cnf(c_5909,plain,
    ( k5_xboole_0(k1_relat_1(sK4),k1_relat_1(sK4)) = k1_relat_1(sK4) ),
    inference(light_normalisation,[status(thm)],[c_5121,c_4264])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f128])).

cnf(c_5910,plain,
    ( k1_relat_1(sK4) = o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5909,c_2])).

cnf(c_20,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) != X0 ),
    inference(cnf_transformation,[],[f134])).

cnf(c_4262,plain,
    ( k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k1_relat_1(sK4))) != sK2 ),
    inference(superposition,[status(thm)],[c_4226,c_20])).

cnf(c_5918,plain,
    ( k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,o_0_0_xboole_0)) != sK2 ),
    inference(demodulation,[status(thm)],[c_5910,c_4262])).

cnf(c_1,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,o_0_0_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f127])).

cnf(c_5973,plain,
    ( sK2 != sK2 ),
    inference(demodulation,[status(thm)],[c_5918,c_1])).

cnf(c_5974,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_5973])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:20:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.12/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.02  
% 2.12/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.12/1.02  
% 2.12/1.02  ------  iProver source info
% 2.12/1.02  
% 2.12/1.02  git: date: 2020-06-30 10:37:57 +0100
% 2.12/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.12/1.02  git: non_committed_changes: false
% 2.12/1.02  git: last_make_outside_of_git: false
% 2.12/1.02  
% 2.12/1.02  ------ 
% 2.12/1.02  
% 2.12/1.02  ------ Input Options
% 2.12/1.02  
% 2.12/1.02  --out_options                           all
% 2.12/1.02  --tptp_safe_out                         true
% 2.12/1.02  --problem_path                          ""
% 2.12/1.02  --include_path                          ""
% 2.12/1.02  --clausifier                            res/vclausify_rel
% 2.12/1.02  --clausifier_options                    --mode clausify
% 2.12/1.02  --stdin                                 false
% 2.12/1.02  --stats_out                             all
% 2.12/1.02  
% 2.12/1.02  ------ General Options
% 2.12/1.02  
% 2.12/1.02  --fof                                   false
% 2.12/1.02  --time_out_real                         305.
% 2.12/1.02  --time_out_virtual                      -1.
% 2.12/1.02  --symbol_type_check                     false
% 2.12/1.02  --clausify_out                          false
% 2.12/1.02  --sig_cnt_out                           false
% 2.12/1.02  --trig_cnt_out                          false
% 2.12/1.02  --trig_cnt_out_tolerance                1.
% 2.12/1.02  --trig_cnt_out_sk_spl                   false
% 2.12/1.02  --abstr_cl_out                          false
% 2.12/1.02  
% 2.12/1.02  ------ Global Options
% 2.12/1.02  
% 2.12/1.02  --schedule                              default
% 2.12/1.02  --add_important_lit                     false
% 2.12/1.02  --prop_solver_per_cl                    1000
% 2.12/1.02  --min_unsat_core                        false
% 2.12/1.02  --soft_assumptions                      false
% 2.12/1.02  --soft_lemma_size                       3
% 2.12/1.02  --prop_impl_unit_size                   0
% 2.12/1.02  --prop_impl_unit                        []
% 2.12/1.02  --share_sel_clauses                     true
% 2.12/1.02  --reset_solvers                         false
% 2.12/1.02  --bc_imp_inh                            [conj_cone]
% 2.12/1.02  --conj_cone_tolerance                   3.
% 2.12/1.02  --extra_neg_conj                        none
% 2.12/1.02  --large_theory_mode                     true
% 2.12/1.02  --prolific_symb_bound                   200
% 2.12/1.02  --lt_threshold                          2000
% 2.12/1.02  --clause_weak_htbl                      true
% 2.12/1.02  --gc_record_bc_elim                     false
% 2.12/1.02  
% 2.12/1.02  ------ Preprocessing Options
% 2.12/1.02  
% 2.12/1.02  --preprocessing_flag                    true
% 2.12/1.02  --time_out_prep_mult                    0.1
% 2.12/1.02  --splitting_mode                        input
% 2.12/1.02  --splitting_grd                         true
% 2.12/1.02  --splitting_cvd                         false
% 2.12/1.02  --splitting_cvd_svl                     false
% 2.12/1.02  --splitting_nvd                         32
% 2.12/1.02  --sub_typing                            true
% 2.12/1.02  --prep_gs_sim                           true
% 2.12/1.02  --prep_unflatten                        true
% 2.12/1.02  --prep_res_sim                          true
% 2.12/1.02  --prep_upred                            true
% 2.12/1.02  --prep_sem_filter                       exhaustive
% 2.12/1.02  --prep_sem_filter_out                   false
% 2.12/1.02  --pred_elim                             true
% 2.12/1.02  --res_sim_input                         true
% 2.12/1.02  --eq_ax_congr_red                       true
% 2.12/1.02  --pure_diseq_elim                       true
% 2.12/1.02  --brand_transform                       false
% 2.12/1.02  --non_eq_to_eq                          false
% 2.12/1.02  --prep_def_merge                        true
% 2.12/1.02  --prep_def_merge_prop_impl              false
% 2.12/1.02  --prep_def_merge_mbd                    true
% 2.12/1.02  --prep_def_merge_tr_red                 false
% 2.12/1.02  --prep_def_merge_tr_cl                  false
% 2.12/1.02  --smt_preprocessing                     true
% 2.12/1.02  --smt_ac_axioms                         fast
% 2.12/1.02  --preprocessed_out                      false
% 2.12/1.02  --preprocessed_stats                    false
% 2.12/1.02  
% 2.12/1.02  ------ Abstraction refinement Options
% 2.12/1.02  
% 2.12/1.02  --abstr_ref                             []
% 2.12/1.02  --abstr_ref_prep                        false
% 2.12/1.02  --abstr_ref_until_sat                   false
% 2.12/1.02  --abstr_ref_sig_restrict                funpre
% 2.12/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.12/1.02  --abstr_ref_under                       []
% 2.12/1.02  
% 2.12/1.02  ------ SAT Options
% 2.12/1.02  
% 2.12/1.02  --sat_mode                              false
% 2.12/1.02  --sat_fm_restart_options                ""
% 2.12/1.02  --sat_gr_def                            false
% 2.12/1.02  --sat_epr_types                         true
% 2.12/1.02  --sat_non_cyclic_types                  false
% 2.12/1.02  --sat_finite_models                     false
% 2.12/1.02  --sat_fm_lemmas                         false
% 2.12/1.02  --sat_fm_prep                           false
% 2.12/1.02  --sat_fm_uc_incr                        true
% 2.12/1.02  --sat_out_model                         small
% 2.12/1.02  --sat_out_clauses                       false
% 2.12/1.02  
% 2.12/1.02  ------ QBF Options
% 2.12/1.02  
% 2.12/1.02  --qbf_mode                              false
% 2.12/1.02  --qbf_elim_univ                         false
% 2.12/1.02  --qbf_dom_inst                          none
% 2.12/1.02  --qbf_dom_pre_inst                      false
% 2.12/1.02  --qbf_sk_in                             false
% 2.12/1.02  --qbf_pred_elim                         true
% 2.12/1.02  --qbf_split                             512
% 2.12/1.02  
% 2.12/1.02  ------ BMC1 Options
% 2.12/1.02  
% 2.12/1.02  --bmc1_incremental                      false
% 2.12/1.02  --bmc1_axioms                           reachable_all
% 2.12/1.02  --bmc1_min_bound                        0
% 2.12/1.02  --bmc1_max_bound                        -1
% 2.12/1.02  --bmc1_max_bound_default                -1
% 2.12/1.02  --bmc1_symbol_reachability              true
% 2.12/1.02  --bmc1_property_lemmas                  false
% 2.12/1.02  --bmc1_k_induction                      false
% 2.12/1.02  --bmc1_non_equiv_states                 false
% 2.12/1.02  --bmc1_deadlock                         false
% 2.12/1.02  --bmc1_ucm                              false
% 2.12/1.02  --bmc1_add_unsat_core                   none
% 2.12/1.02  --bmc1_unsat_core_children              false
% 2.12/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.12/1.02  --bmc1_out_stat                         full
% 2.12/1.02  --bmc1_ground_init                      false
% 2.12/1.02  --bmc1_pre_inst_next_state              false
% 2.12/1.02  --bmc1_pre_inst_state                   false
% 2.12/1.02  --bmc1_pre_inst_reach_state             false
% 2.12/1.02  --bmc1_out_unsat_core                   false
% 2.12/1.02  --bmc1_aig_witness_out                  false
% 2.12/1.02  --bmc1_verbose                          false
% 2.12/1.02  --bmc1_dump_clauses_tptp                false
% 2.12/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.12/1.02  --bmc1_dump_file                        -
% 2.12/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.12/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.12/1.02  --bmc1_ucm_extend_mode                  1
% 2.12/1.02  --bmc1_ucm_init_mode                    2
% 2.12/1.02  --bmc1_ucm_cone_mode                    none
% 2.12/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.12/1.02  --bmc1_ucm_relax_model                  4
% 2.12/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.12/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.12/1.02  --bmc1_ucm_layered_model                none
% 2.12/1.02  --bmc1_ucm_max_lemma_size               10
% 2.12/1.02  
% 2.12/1.02  ------ AIG Options
% 2.12/1.02  
% 2.12/1.02  --aig_mode                              false
% 2.12/1.02  
% 2.12/1.02  ------ Instantiation Options
% 2.12/1.02  
% 2.12/1.02  --instantiation_flag                    true
% 2.12/1.02  --inst_sos_flag                         false
% 2.12/1.02  --inst_sos_phase                        true
% 2.12/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.12/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.12/1.02  --inst_lit_sel_side                     num_symb
% 2.12/1.02  --inst_solver_per_active                1400
% 2.12/1.02  --inst_solver_calls_frac                1.
% 2.12/1.02  --inst_passive_queue_type               priority_queues
% 2.12/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.12/1.02  --inst_passive_queues_freq              [25;2]
% 2.12/1.02  --inst_dismatching                      true
% 2.12/1.02  --inst_eager_unprocessed_to_passive     true
% 2.12/1.02  --inst_prop_sim_given                   true
% 2.12/1.02  --inst_prop_sim_new                     false
% 2.12/1.02  --inst_subs_new                         false
% 2.12/1.02  --inst_eq_res_simp                      false
% 2.12/1.02  --inst_subs_given                       false
% 2.12/1.02  --inst_orphan_elimination               true
% 2.12/1.02  --inst_learning_loop_flag               true
% 2.12/1.02  --inst_learning_start                   3000
% 2.12/1.02  --inst_learning_factor                  2
% 2.12/1.02  --inst_start_prop_sim_after_learn       3
% 2.12/1.02  --inst_sel_renew                        solver
% 2.12/1.02  --inst_lit_activity_flag                true
% 2.12/1.02  --inst_restr_to_given                   false
% 2.12/1.02  --inst_activity_threshold               500
% 2.12/1.02  --inst_out_proof                        true
% 2.12/1.02  
% 2.12/1.02  ------ Resolution Options
% 2.12/1.02  
% 2.12/1.02  --resolution_flag                       true
% 2.12/1.02  --res_lit_sel                           adaptive
% 2.12/1.02  --res_lit_sel_side                      none
% 2.12/1.02  --res_ordering                          kbo
% 2.12/1.02  --res_to_prop_solver                    active
% 2.12/1.02  --res_prop_simpl_new                    false
% 2.12/1.02  --res_prop_simpl_given                  true
% 2.12/1.02  --res_passive_queue_type                priority_queues
% 2.12/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.12/1.02  --res_passive_queues_freq               [15;5]
% 2.12/1.02  --res_forward_subs                      full
% 2.12/1.02  --res_backward_subs                     full
% 2.12/1.02  --res_forward_subs_resolution           true
% 2.12/1.02  --res_backward_subs_resolution          true
% 2.12/1.02  --res_orphan_elimination                true
% 2.12/1.02  --res_time_limit                        2.
% 2.12/1.02  --res_out_proof                         true
% 2.12/1.02  
% 2.12/1.02  ------ Superposition Options
% 2.12/1.02  
% 2.12/1.02  --superposition_flag                    true
% 2.12/1.02  --sup_passive_queue_type                priority_queues
% 2.12/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.12/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.12/1.02  --demod_completeness_check              fast
% 2.12/1.02  --demod_use_ground                      true
% 2.12/1.02  --sup_to_prop_solver                    passive
% 2.12/1.02  --sup_prop_simpl_new                    true
% 2.12/1.02  --sup_prop_simpl_given                  true
% 2.12/1.02  --sup_fun_splitting                     false
% 2.12/1.02  --sup_smt_interval                      50000
% 2.12/1.02  
% 2.12/1.02  ------ Superposition Simplification Setup
% 2.12/1.02  
% 2.12/1.02  --sup_indices_passive                   []
% 2.12/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.12/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.12/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.12/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.12/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.12/1.02  --sup_full_bw                           [BwDemod]
% 2.12/1.02  --sup_immed_triv                        [TrivRules]
% 2.12/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.12/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.12/1.02  --sup_immed_bw_main                     []
% 2.12/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.12/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.12/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.12/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.12/1.02  
% 2.12/1.02  ------ Combination Options
% 2.12/1.02  
% 2.12/1.02  --comb_res_mult                         3
% 2.12/1.02  --comb_sup_mult                         2
% 2.12/1.02  --comb_inst_mult                        10
% 2.12/1.02  
% 2.12/1.02  ------ Debug Options
% 2.12/1.02  
% 2.12/1.02  --dbg_backtrace                         false
% 2.12/1.02  --dbg_dump_prop_clauses                 false
% 2.12/1.02  --dbg_dump_prop_clauses_file            -
% 2.12/1.02  --dbg_out_stat                          false
% 2.12/1.02  ------ Parsing...
% 2.12/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.12/1.02  
% 2.12/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.12/1.02  
% 2.12/1.02  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.12/1.02  
% 2.12/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.12/1.02  ------ Proving...
% 2.12/1.02  ------ Problem Properties 
% 2.12/1.02  
% 2.12/1.02  
% 2.12/1.02  clauses                                 32
% 2.12/1.02  conjectures                             3
% 2.12/1.03  EPR                                     3
% 2.12/1.03  Horn                                    26
% 2.12/1.03  unary                                   10
% 2.12/1.03  binary                                  8
% 2.12/1.03  lits                                    73
% 2.12/1.03  lits eq                                 21
% 2.12/1.03  fd_pure                                 0
% 2.12/1.03  fd_pseudo                               0
% 2.12/1.03  fd_cond                                 2
% 2.12/1.03  fd_pseudo_cond                          1
% 2.12/1.03  AC symbols                              0
% 2.12/1.03  
% 2.12/1.03  ------ Schedule dynamic 5 is on 
% 2.12/1.03  
% 2.12/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.12/1.03  
% 2.12/1.03  
% 2.12/1.03  ------ 
% 2.12/1.03  Current options:
% 2.12/1.03  ------ 
% 2.12/1.03  
% 2.12/1.03  ------ Input Options
% 2.12/1.03  
% 2.12/1.03  --out_options                           all
% 2.12/1.03  --tptp_safe_out                         true
% 2.12/1.03  --problem_path                          ""
% 2.12/1.03  --include_path                          ""
% 2.12/1.03  --clausifier                            res/vclausify_rel
% 2.12/1.03  --clausifier_options                    --mode clausify
% 2.12/1.03  --stdin                                 false
% 2.12/1.03  --stats_out                             all
% 2.12/1.03  
% 2.12/1.03  ------ General Options
% 2.12/1.03  
% 2.12/1.03  --fof                                   false
% 2.12/1.03  --time_out_real                         305.
% 2.12/1.03  --time_out_virtual                      -1.
% 2.12/1.03  --symbol_type_check                     false
% 2.12/1.03  --clausify_out                          false
% 2.12/1.03  --sig_cnt_out                           false
% 2.12/1.03  --trig_cnt_out                          false
% 2.12/1.03  --trig_cnt_out_tolerance                1.
% 2.12/1.03  --trig_cnt_out_sk_spl                   false
% 2.12/1.03  --abstr_cl_out                          false
% 2.12/1.03  
% 2.12/1.03  ------ Global Options
% 2.12/1.03  
% 2.12/1.03  --schedule                              default
% 2.12/1.03  --add_important_lit                     false
% 2.12/1.03  --prop_solver_per_cl                    1000
% 2.12/1.03  --min_unsat_core                        false
% 2.12/1.03  --soft_assumptions                      false
% 2.12/1.03  --soft_lemma_size                       3
% 2.12/1.03  --prop_impl_unit_size                   0
% 2.12/1.03  --prop_impl_unit                        []
% 2.12/1.03  --share_sel_clauses                     true
% 2.12/1.03  --reset_solvers                         false
% 2.12/1.03  --bc_imp_inh                            [conj_cone]
% 2.12/1.03  --conj_cone_tolerance                   3.
% 2.12/1.03  --extra_neg_conj                        none
% 2.12/1.03  --large_theory_mode                     true
% 2.12/1.03  --prolific_symb_bound                   200
% 2.12/1.03  --lt_threshold                          2000
% 2.12/1.03  --clause_weak_htbl                      true
% 2.12/1.03  --gc_record_bc_elim                     false
% 2.12/1.03  
% 2.12/1.03  ------ Preprocessing Options
% 2.12/1.03  
% 2.12/1.03  --preprocessing_flag                    true
% 2.12/1.03  --time_out_prep_mult                    0.1
% 2.12/1.03  --splitting_mode                        input
% 2.12/1.03  --splitting_grd                         true
% 2.12/1.03  --splitting_cvd                         false
% 2.12/1.03  --splitting_cvd_svl                     false
% 2.12/1.03  --splitting_nvd                         32
% 2.12/1.03  --sub_typing                            true
% 2.12/1.03  --prep_gs_sim                           true
% 2.12/1.03  --prep_unflatten                        true
% 2.12/1.03  --prep_res_sim                          true
% 2.12/1.03  --prep_upred                            true
% 2.12/1.03  --prep_sem_filter                       exhaustive
% 2.12/1.03  --prep_sem_filter_out                   false
% 2.12/1.03  --pred_elim                             true
% 2.12/1.03  --res_sim_input                         true
% 2.12/1.03  --eq_ax_congr_red                       true
% 2.12/1.03  --pure_diseq_elim                       true
% 2.12/1.03  --brand_transform                       false
% 2.12/1.03  --non_eq_to_eq                          false
% 2.12/1.03  --prep_def_merge                        true
% 2.12/1.03  --prep_def_merge_prop_impl              false
% 2.12/1.03  --prep_def_merge_mbd                    true
% 2.12/1.03  --prep_def_merge_tr_red                 false
% 2.12/1.03  --prep_def_merge_tr_cl                  false
% 2.12/1.03  --smt_preprocessing                     true
% 2.12/1.03  --smt_ac_axioms                         fast
% 2.12/1.03  --preprocessed_out                      false
% 2.12/1.03  --preprocessed_stats                    false
% 2.12/1.03  
% 2.12/1.03  ------ Abstraction refinement Options
% 2.12/1.03  
% 2.12/1.03  --abstr_ref                             []
% 2.12/1.03  --abstr_ref_prep                        false
% 2.12/1.03  --abstr_ref_until_sat                   false
% 2.12/1.03  --abstr_ref_sig_restrict                funpre
% 2.12/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.12/1.03  --abstr_ref_under                       []
% 2.12/1.03  
% 2.12/1.03  ------ SAT Options
% 2.12/1.03  
% 2.12/1.03  --sat_mode                              false
% 2.12/1.03  --sat_fm_restart_options                ""
% 2.12/1.03  --sat_gr_def                            false
% 2.12/1.03  --sat_epr_types                         true
% 2.12/1.03  --sat_non_cyclic_types                  false
% 2.12/1.03  --sat_finite_models                     false
% 2.12/1.03  --sat_fm_lemmas                         false
% 2.12/1.03  --sat_fm_prep                           false
% 2.12/1.03  --sat_fm_uc_incr                        true
% 2.12/1.03  --sat_out_model                         small
% 2.12/1.03  --sat_out_clauses                       false
% 2.12/1.03  
% 2.12/1.03  ------ QBF Options
% 2.12/1.03  
% 2.12/1.03  --qbf_mode                              false
% 2.12/1.03  --qbf_elim_univ                         false
% 2.12/1.03  --qbf_dom_inst                          none
% 2.12/1.03  --qbf_dom_pre_inst                      false
% 2.12/1.03  --qbf_sk_in                             false
% 2.12/1.03  --qbf_pred_elim                         true
% 2.12/1.03  --qbf_split                             512
% 2.12/1.03  
% 2.12/1.03  ------ BMC1 Options
% 2.12/1.03  
% 2.12/1.03  --bmc1_incremental                      false
% 2.12/1.03  --bmc1_axioms                           reachable_all
% 2.12/1.03  --bmc1_min_bound                        0
% 2.12/1.03  --bmc1_max_bound                        -1
% 2.12/1.03  --bmc1_max_bound_default                -1
% 2.12/1.03  --bmc1_symbol_reachability              true
% 2.12/1.03  --bmc1_property_lemmas                  false
% 2.12/1.03  --bmc1_k_induction                      false
% 2.12/1.03  --bmc1_non_equiv_states                 false
% 2.12/1.03  --bmc1_deadlock                         false
% 2.12/1.03  --bmc1_ucm                              false
% 2.12/1.03  --bmc1_add_unsat_core                   none
% 2.12/1.03  --bmc1_unsat_core_children              false
% 2.12/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.12/1.03  --bmc1_out_stat                         full
% 2.12/1.03  --bmc1_ground_init                      false
% 2.12/1.03  --bmc1_pre_inst_next_state              false
% 2.12/1.03  --bmc1_pre_inst_state                   false
% 2.12/1.03  --bmc1_pre_inst_reach_state             false
% 2.12/1.03  --bmc1_out_unsat_core                   false
% 2.12/1.03  --bmc1_aig_witness_out                  false
% 2.12/1.03  --bmc1_verbose                          false
% 2.12/1.03  --bmc1_dump_clauses_tptp                false
% 2.12/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.12/1.03  --bmc1_dump_file                        -
% 2.12/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.12/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.12/1.03  --bmc1_ucm_extend_mode                  1
% 2.12/1.03  --bmc1_ucm_init_mode                    2
% 2.12/1.03  --bmc1_ucm_cone_mode                    none
% 2.12/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.12/1.03  --bmc1_ucm_relax_model                  4
% 2.12/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.12/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.12/1.03  --bmc1_ucm_layered_model                none
% 2.12/1.03  --bmc1_ucm_max_lemma_size               10
% 2.12/1.03  
% 2.12/1.03  ------ AIG Options
% 2.12/1.03  
% 2.12/1.03  --aig_mode                              false
% 2.12/1.03  
% 2.12/1.03  ------ Instantiation Options
% 2.12/1.03  
% 2.12/1.03  --instantiation_flag                    true
% 2.12/1.03  --inst_sos_flag                         false
% 2.12/1.03  --inst_sos_phase                        true
% 2.12/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.12/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.12/1.03  --inst_lit_sel_side                     none
% 2.12/1.03  --inst_solver_per_active                1400
% 2.12/1.03  --inst_solver_calls_frac                1.
% 2.12/1.03  --inst_passive_queue_type               priority_queues
% 2.12/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.12/1.03  --inst_passive_queues_freq              [25;2]
% 2.12/1.03  --inst_dismatching                      true
% 2.12/1.03  --inst_eager_unprocessed_to_passive     true
% 2.12/1.03  --inst_prop_sim_given                   true
% 2.12/1.03  --inst_prop_sim_new                     false
% 2.12/1.03  --inst_subs_new                         false
% 2.12/1.03  --inst_eq_res_simp                      false
% 2.12/1.03  --inst_subs_given                       false
% 2.12/1.03  --inst_orphan_elimination               true
% 2.12/1.03  --inst_learning_loop_flag               true
% 2.12/1.03  --inst_learning_start                   3000
% 2.12/1.03  --inst_learning_factor                  2
% 2.12/1.03  --inst_start_prop_sim_after_learn       3
% 2.12/1.03  --inst_sel_renew                        solver
% 2.12/1.03  --inst_lit_activity_flag                true
% 2.12/1.03  --inst_restr_to_given                   false
% 2.12/1.03  --inst_activity_threshold               500
% 2.12/1.03  --inst_out_proof                        true
% 2.12/1.03  
% 2.12/1.03  ------ Resolution Options
% 2.12/1.03  
% 2.12/1.03  --resolution_flag                       false
% 2.12/1.03  --res_lit_sel                           adaptive
% 2.12/1.03  --res_lit_sel_side                      none
% 2.12/1.03  --res_ordering                          kbo
% 2.12/1.03  --res_to_prop_solver                    active
% 2.12/1.03  --res_prop_simpl_new                    false
% 2.12/1.03  --res_prop_simpl_given                  true
% 2.12/1.03  --res_passive_queue_type                priority_queues
% 2.12/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.12/1.03  --res_passive_queues_freq               [15;5]
% 2.12/1.03  --res_forward_subs                      full
% 2.12/1.03  --res_backward_subs                     full
% 2.12/1.03  --res_forward_subs_resolution           true
% 2.12/1.03  --res_backward_subs_resolution          true
% 2.12/1.03  --res_orphan_elimination                true
% 2.12/1.03  --res_time_limit                        2.
% 2.12/1.03  --res_out_proof                         true
% 2.12/1.03  
% 2.12/1.03  ------ Superposition Options
% 2.12/1.03  
% 2.12/1.03  --superposition_flag                    true
% 2.12/1.03  --sup_passive_queue_type                priority_queues
% 2.12/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.12/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.12/1.03  --demod_completeness_check              fast
% 2.12/1.03  --demod_use_ground                      true
% 2.12/1.03  --sup_to_prop_solver                    passive
% 2.12/1.03  --sup_prop_simpl_new                    true
% 2.12/1.03  --sup_prop_simpl_given                  true
% 2.12/1.03  --sup_fun_splitting                     false
% 2.12/1.03  --sup_smt_interval                      50000
% 2.12/1.03  
% 2.12/1.03  ------ Superposition Simplification Setup
% 2.12/1.03  
% 2.12/1.03  --sup_indices_passive                   []
% 2.12/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.12/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.12/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.12/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.12/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.12/1.03  --sup_full_bw                           [BwDemod]
% 2.12/1.03  --sup_immed_triv                        [TrivRules]
% 2.12/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.12/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.12/1.03  --sup_immed_bw_main                     []
% 2.12/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.12/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.12/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.12/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.12/1.03  
% 2.12/1.03  ------ Combination Options
% 2.12/1.03  
% 2.12/1.03  --comb_res_mult                         3
% 2.12/1.03  --comb_sup_mult                         2
% 2.12/1.03  --comb_inst_mult                        10
% 2.12/1.03  
% 2.12/1.03  ------ Debug Options
% 2.12/1.03  
% 2.12/1.03  --dbg_backtrace                         false
% 2.12/1.03  --dbg_dump_prop_clauses                 false
% 2.12/1.03  --dbg_dump_prop_clauses_file            -
% 2.12/1.03  --dbg_out_stat                          false
% 2.12/1.03  
% 2.12/1.03  
% 2.12/1.03  
% 2.12/1.03  
% 2.12/1.03  ------ Proving...
% 2.12/1.03  
% 2.12/1.03  
% 2.12/1.03  % SZS status Theorem for theBenchmark.p
% 2.12/1.03  
% 2.12/1.03   Resolution empty clause
% 2.12/1.03  
% 2.12/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 2.12/1.03  
% 2.12/1.03  fof(f15,axiom,(
% 2.12/1.03    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 2.12/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.12/1.03  
% 2.12/1.03  fof(f54,plain,(
% 2.12/1.03    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 2.12/1.03    inference(nnf_transformation,[],[f15])).
% 2.12/1.03  
% 2.12/1.03  fof(f82,plain,(
% 2.12/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 2.12/1.03    inference(cnf_transformation,[],[f54])).
% 2.12/1.03  
% 2.12/1.03  fof(f3,axiom,(
% 2.12/1.03    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.12/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.12/1.03  
% 2.12/1.03  fof(f69,plain,(
% 2.12/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.12/1.03    inference(cnf_transformation,[],[f3])).
% 2.12/1.03  
% 2.12/1.03  fof(f17,axiom,(
% 2.12/1.03    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.12/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.12/1.03  
% 2.12/1.03  fof(f85,plain,(
% 2.12/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.12/1.03    inference(cnf_transformation,[],[f17])).
% 2.12/1.03  
% 2.12/1.03  fof(f121,plain,(
% 2.12/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.12/1.03    inference(definition_unfolding,[],[f85,f120])).
% 2.12/1.03  
% 2.12/1.03  fof(f122,plain,(
% 2.12/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.12/1.03    inference(definition_unfolding,[],[f69,f121])).
% 2.12/1.03  
% 2.12/1.03  fof(f6,axiom,(
% 2.12/1.03    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.12/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.12/1.03  
% 2.12/1.03  fof(f72,plain,(
% 2.12/1.03    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.12/1.03    inference(cnf_transformation,[],[f6])).
% 2.12/1.03  
% 2.12/1.03  fof(f7,axiom,(
% 2.12/1.03    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.12/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.12/1.03  
% 2.12/1.03  fof(f73,plain,(
% 2.12/1.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.12/1.03    inference(cnf_transformation,[],[f7])).
% 2.12/1.03  
% 2.12/1.03  fof(f8,axiom,(
% 2.12/1.03    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.12/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.12/1.03  
% 2.12/1.03  fof(f74,plain,(
% 2.12/1.03    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.12/1.03    inference(cnf_transformation,[],[f8])).
% 2.12/1.03  
% 2.12/1.03  fof(f9,axiom,(
% 2.12/1.03    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.12/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.12/1.03  
% 2.12/1.03  fof(f75,plain,(
% 2.12/1.03    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.12/1.03    inference(cnf_transformation,[],[f9])).
% 2.12/1.03  
% 2.12/1.03  fof(f10,axiom,(
% 2.12/1.03    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.12/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.12/1.03  
% 2.12/1.03  fof(f76,plain,(
% 2.12/1.03    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.12/1.03    inference(cnf_transformation,[],[f10])).
% 2.12/1.03  
% 2.12/1.03  fof(f11,axiom,(
% 2.12/1.03    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.12/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.12/1.03  
% 2.12/1.03  fof(f77,plain,(
% 2.12/1.03    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.12/1.03    inference(cnf_transformation,[],[f11])).
% 2.12/1.03  
% 2.12/1.03  fof(f12,axiom,(
% 2.12/1.03    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 2.12/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.12/1.03  
% 2.12/1.03  fof(f78,plain,(
% 2.12/1.03    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 2.12/1.03    inference(cnf_transformation,[],[f12])).
% 2.12/1.03  
% 2.12/1.03  fof(f116,plain,(
% 2.12/1.03    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.12/1.03    inference(definition_unfolding,[],[f77,f78])).
% 2.12/1.03  
% 2.12/1.03  fof(f117,plain,(
% 2.12/1.03    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.12/1.03    inference(definition_unfolding,[],[f76,f116])).
% 2.12/1.03  
% 2.12/1.03  fof(f118,plain,(
% 2.12/1.03    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.12/1.03    inference(definition_unfolding,[],[f75,f117])).
% 2.12/1.03  
% 2.12/1.03  fof(f119,plain,(
% 2.12/1.03    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.12/1.03    inference(definition_unfolding,[],[f74,f118])).
% 2.12/1.03  
% 2.12/1.03  fof(f120,plain,(
% 2.12/1.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.12/1.03    inference(definition_unfolding,[],[f73,f119])).
% 2.12/1.03  
% 2.12/1.03  fof(f124,plain,(
% 2.12/1.03    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.12/1.03    inference(definition_unfolding,[],[f72,f120])).
% 2.12/1.03  
% 2.12/1.03  fof(f130,plain,(
% 2.12/1.03    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) = X0 | r2_hidden(X1,X0)) )),
% 2.12/1.03    inference(definition_unfolding,[],[f82,f122,f124])).
% 2.12/1.03  
% 2.12/1.03  fof(f31,conjecture,(
% 2.12/1.03    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 2.12/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.12/1.03  
% 2.12/1.03  fof(f32,negated_conjecture,(
% 2.12/1.03    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 2.12/1.03    inference(negated_conjecture,[],[f31])).
% 2.12/1.03  
% 2.12/1.03  fof(f52,plain,(
% 2.12/1.03    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 2.12/1.03    inference(ennf_transformation,[],[f32])).
% 2.12/1.03  
% 2.12/1.03  fof(f53,plain,(
% 2.12/1.03    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 2.12/1.03    inference(flattening,[],[f52])).
% 2.12/1.03  
% 2.12/1.03  fof(f65,plain,(
% 2.12/1.03    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (~r2_hidden(k1_funct_1(sK4,sK2),sK3) & k1_xboole_0 != sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) & v1_funct_2(sK4,k1_tarski(sK2),sK3) & v1_funct_1(sK4))),
% 2.12/1.03    introduced(choice_axiom,[])).
% 2.12/1.03  
% 2.12/1.03  fof(f66,plain,(
% 2.12/1.03    ~r2_hidden(k1_funct_1(sK4,sK2),sK3) & k1_xboole_0 != sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) & v1_funct_2(sK4,k1_tarski(sK2),sK3) & v1_funct_1(sK4)),
% 2.12/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f53,f65])).
% 2.12/1.03  
% 2.12/1.03  fof(f113,plain,(
% 2.12/1.03    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))),
% 2.12/1.03    inference(cnf_transformation,[],[f66])).
% 2.12/1.03  
% 2.12/1.03  fof(f143,plain,(
% 2.12/1.03    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))),
% 2.12/1.03    inference(definition_unfolding,[],[f113,f124])).
% 2.12/1.03  
% 2.12/1.03  fof(f27,axiom,(
% 2.12/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.12/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.12/1.03  
% 2.12/1.03  fof(f46,plain,(
% 2.12/1.03    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.12/1.03    inference(ennf_transformation,[],[f27])).
% 2.12/1.03  
% 2.12/1.03  fof(f102,plain,(
% 2.12/1.03    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.12/1.03    inference(cnf_transformation,[],[f46])).
% 2.12/1.03  
% 2.12/1.03  fof(f29,axiom,(
% 2.12/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.12/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.12/1.03  
% 2.12/1.03  fof(f48,plain,(
% 2.12/1.03    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.12/1.03    inference(ennf_transformation,[],[f29])).
% 2.12/1.03  
% 2.12/1.03  fof(f49,plain,(
% 2.12/1.03    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.12/1.03    inference(flattening,[],[f48])).
% 2.12/1.03  
% 2.12/1.03  fof(f64,plain,(
% 2.12/1.03    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.12/1.03    inference(nnf_transformation,[],[f49])).
% 2.12/1.03  
% 2.12/1.03  fof(f104,plain,(
% 2.12/1.03    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.12/1.03    inference(cnf_transformation,[],[f64])).
% 2.12/1.03  
% 2.12/1.03  fof(f1,axiom,(
% 2.12/1.03    k1_xboole_0 = o_0_0_xboole_0),
% 2.12/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.12/1.03  
% 2.12/1.03  fof(f67,plain,(
% 2.12/1.03    k1_xboole_0 = o_0_0_xboole_0),
% 2.12/1.03    inference(cnf_transformation,[],[f1])).
% 2.12/1.03  
% 2.12/1.03  fof(f140,plain,(
% 2.12/1.03    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | o_0_0_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.12/1.03    inference(definition_unfolding,[],[f104,f67])).
% 2.12/1.03  
% 2.12/1.03  fof(f112,plain,(
% 2.12/1.03    v1_funct_2(sK4,k1_tarski(sK2),sK3)),
% 2.12/1.03    inference(cnf_transformation,[],[f66])).
% 2.12/1.03  
% 2.12/1.03  fof(f144,plain,(
% 2.12/1.03    v1_funct_2(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)),
% 2.12/1.03    inference(definition_unfolding,[],[f112,f124])).
% 2.12/1.03  
% 2.12/1.03  fof(f114,plain,(
% 2.12/1.03    k1_xboole_0 != sK3),
% 2.12/1.03    inference(cnf_transformation,[],[f66])).
% 2.12/1.03  
% 2.12/1.03  fof(f142,plain,(
% 2.12/1.03    o_0_0_xboole_0 != sK3),
% 2.12/1.03    inference(definition_unfolding,[],[f114,f67])).
% 2.12/1.03  
% 2.12/1.03  fof(f30,axiom,(
% 2.12/1.03    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 2.12/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.12/1.03  
% 2.12/1.03  fof(f50,plain,(
% 2.12/1.03    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.12/1.03    inference(ennf_transformation,[],[f30])).
% 2.12/1.03  
% 2.12/1.03  fof(f51,plain,(
% 2.12/1.03    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.12/1.03    inference(flattening,[],[f50])).
% 2.12/1.03  
% 2.12/1.03  fof(f110,plain,(
% 2.12/1.03    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.12/1.03    inference(cnf_transformation,[],[f51])).
% 2.12/1.03  
% 2.12/1.03  fof(f141,plain,(
% 2.12/1.03    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),X1) | o_0_0_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.12/1.03    inference(definition_unfolding,[],[f110,f67])).
% 2.12/1.03  
% 2.12/1.03  fof(f111,plain,(
% 2.12/1.03    v1_funct_1(sK4)),
% 2.12/1.03    inference(cnf_transformation,[],[f66])).
% 2.12/1.03  
% 2.12/1.03  fof(f115,plain,(
% 2.12/1.03    ~r2_hidden(k1_funct_1(sK4,sK2),sK3)),
% 2.12/1.03    inference(cnf_transformation,[],[f66])).
% 2.12/1.03  
% 2.12/1.03  fof(f14,axiom,(
% 2.12/1.03    ! [X0,X1] : k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_tarski(X0)),
% 2.12/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.12/1.03  
% 2.12/1.03  fof(f80,plain,(
% 2.12/1.03    ( ! [X0,X1] : (k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_tarski(X0)) )),
% 2.12/1.03    inference(cnf_transformation,[],[f14])).
% 2.12/1.03  
% 2.12/1.03  fof(f129,plain,(
% 2.12/1.03    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.12/1.03    inference(definition_unfolding,[],[f80,f121,f124,f120,f124])).
% 2.12/1.03  
% 2.12/1.03  fof(f5,axiom,(
% 2.12/1.03    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 2.12/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.12/1.03  
% 2.12/1.03  fof(f71,plain,(
% 2.12/1.03    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.12/1.03    inference(cnf_transformation,[],[f5])).
% 2.12/1.03  
% 2.12/1.03  fof(f128,plain,(
% 2.12/1.03    ( ! [X0] : (o_0_0_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.12/1.03    inference(definition_unfolding,[],[f71,f67])).
% 2.12/1.03  
% 2.12/1.03  fof(f24,axiom,(
% 2.12/1.03    ! [X0] : k1_ordinal1(X0) != X0),
% 2.12/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.12/1.03  
% 2.12/1.03  fof(f99,plain,(
% 2.12/1.03    ( ! [X0] : (k1_ordinal1(X0) != X0) )),
% 2.12/1.03    inference(cnf_transformation,[],[f24])).
% 2.12/1.03  
% 2.12/1.03  fof(f23,axiom,(
% 2.12/1.03    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)),
% 2.12/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.12/1.03  
% 2.12/1.03  fof(f98,plain,(
% 2.12/1.03    ( ! [X0] : (k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)) )),
% 2.12/1.03    inference(cnf_transformation,[],[f23])).
% 2.12/1.03  
% 2.12/1.03  fof(f13,axiom,(
% 2.12/1.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.12/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.12/1.03  
% 2.12/1.03  fof(f79,plain,(
% 2.12/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.12/1.03    inference(cnf_transformation,[],[f13])).
% 2.12/1.03  
% 2.12/1.03  fof(f123,plain,(
% 2.12/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.12/1.03    inference(definition_unfolding,[],[f79,f120])).
% 2.12/1.03  
% 2.12/1.03  fof(f125,plain,(
% 2.12/1.03    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k1_ordinal1(X0)) )),
% 2.12/1.03    inference(definition_unfolding,[],[f98,f123,f124])).
% 2.12/1.03  
% 2.12/1.03  fof(f134,plain,(
% 2.12/1.03    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) != X0) )),
% 2.12/1.03    inference(definition_unfolding,[],[f99,f125])).
% 2.12/1.03  
% 2.12/1.03  fof(f4,axiom,(
% 2.12/1.03    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.12/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.12/1.03  
% 2.12/1.03  fof(f70,plain,(
% 2.12/1.03    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.12/1.03    inference(cnf_transformation,[],[f4])).
% 2.12/1.03  
% 2.12/1.03  fof(f127,plain,(
% 2.12/1.03    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,o_0_0_xboole_0)) = X0) )),
% 2.12/1.03    inference(definition_unfolding,[],[f70,f123,f67])).
% 2.12/1.03  
% 2.12/1.03  cnf(c_4,plain,
% 2.12/1.03      ( r2_hidden(X0,X1)
% 2.12/1.03      | k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = X1 ),
% 2.12/1.03      inference(cnf_transformation,[],[f130]) ).
% 2.12/1.03  
% 2.12/1.03  cnf(c_2412,plain,
% 2.12/1.03      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) = X0
% 2.12/1.03      | r2_hidden(X1,X0) = iProver_top ),
% 2.12/1.03      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.12/1.03  
% 2.12/1.03  cnf(c_34,negated_conjecture,
% 2.12/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) ),
% 2.12/1.03      inference(cnf_transformation,[],[f143]) ).
% 2.12/1.03  
% 2.12/1.03  cnf(c_2403,plain,
% 2.12/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) = iProver_top ),
% 2.12/1.03      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.12/1.03  
% 2.12/1.03  cnf(c_23,plain,
% 2.12/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.12/1.03      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.12/1.03      inference(cnf_transformation,[],[f102]) ).
% 2.12/1.03  
% 2.12/1.03  cnf(c_2406,plain,
% 2.12/1.03      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.12/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.12/1.03      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.12/1.03  
% 2.12/1.03  cnf(c_3935,plain,
% 2.12/1.03      ( k1_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4) = k1_relat_1(sK4) ),
% 2.12/1.03      inference(superposition,[status(thm)],[c_2403,c_2406]) ).
% 2.12/1.03  
% 2.12/1.03  cnf(c_30,plain,
% 2.12/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 2.12/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.12/1.03      | k1_relset_1(X1,X2,X0) = X1
% 2.12/1.03      | o_0_0_xboole_0 = X2 ),
% 2.12/1.03      inference(cnf_transformation,[],[f140]) ).
% 2.12/1.03  
% 2.12/1.03  cnf(c_35,negated_conjecture,
% 2.12/1.03      ( v1_funct_2(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) ),
% 2.12/1.03      inference(cnf_transformation,[],[f144]) ).
% 2.12/1.03  
% 2.12/1.03  cnf(c_1156,plain,
% 2.12/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.12/1.03      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != X1
% 2.12/1.03      | k1_relset_1(X1,X2,X0) = X1
% 2.12/1.03      | sK3 != X2
% 2.12/1.03      | sK4 != X0
% 2.12/1.03      | o_0_0_xboole_0 = X2 ),
% 2.12/1.03      inference(resolution_lifted,[status(thm)],[c_30,c_35]) ).
% 2.12/1.03  
% 2.12/1.03  cnf(c_1157,plain,
% 2.12/1.03      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))
% 2.12/1.03      | k1_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 2.12/1.03      | o_0_0_xboole_0 = sK3 ),
% 2.12/1.03      inference(unflattening,[status(thm)],[c_1156]) ).
% 2.12/1.03  
% 2.12/1.03  cnf(c_33,negated_conjecture,
% 2.12/1.03      ( o_0_0_xboole_0 != sK3 ),
% 2.12/1.03      inference(cnf_transformation,[],[f142]) ).
% 2.12/1.03  
% 2.12/1.03  cnf(c_1159,plain,
% 2.12/1.03      ( k1_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 2.12/1.03      inference(global_propositional_subsumption,
% 2.12/1.03                [status(thm)],
% 2.12/1.03                [c_1157,c_34,c_33]) ).
% 2.12/1.03  
% 2.12/1.03  cnf(c_4226,plain,
% 2.12/1.03      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_relat_1(sK4) ),
% 2.12/1.03      inference(demodulation,[status(thm)],[c_3935,c_1159]) ).
% 2.12/1.03  
% 2.12/1.03  cnf(c_31,plain,
% 2.12/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 2.12/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.12/1.03      | ~ r2_hidden(X3,X1)
% 2.12/1.03      | r2_hidden(k1_funct_1(X0,X3),X2)
% 2.12/1.03      | ~ v1_funct_1(X0)
% 2.12/1.03      | o_0_0_xboole_0 = X2 ),
% 2.12/1.03      inference(cnf_transformation,[],[f141]) ).
% 2.12/1.03  
% 2.12/1.03  cnf(c_36,negated_conjecture,
% 2.12/1.03      ( v1_funct_1(sK4) ),
% 2.12/1.03      inference(cnf_transformation,[],[f111]) ).
% 2.12/1.03  
% 2.12/1.03  cnf(c_605,plain,
% 2.12/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 2.12/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.12/1.03      | ~ r2_hidden(X3,X1)
% 2.12/1.03      | r2_hidden(k1_funct_1(X0,X3),X2)
% 2.12/1.03      | sK4 != X0
% 2.12/1.03      | o_0_0_xboole_0 = X2 ),
% 2.12/1.03      inference(resolution_lifted,[status(thm)],[c_31,c_36]) ).
% 2.12/1.03  
% 2.12/1.03  cnf(c_606,plain,
% 2.12/1.03      ( ~ v1_funct_2(sK4,X0,X1)
% 2.12/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.12/1.03      | ~ r2_hidden(X2,X0)
% 2.12/1.03      | r2_hidden(k1_funct_1(sK4,X2),X1)
% 2.12/1.03      | o_0_0_xboole_0 = X1 ),
% 2.12/1.03      inference(unflattening,[status(thm)],[c_605]) ).
% 2.12/1.03  
% 2.12/1.03  cnf(c_1183,plain,
% 2.12/1.03      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.12/1.03      | ~ r2_hidden(X2,X0)
% 2.12/1.03      | r2_hidden(k1_funct_1(sK4,X2),X1)
% 2.12/1.03      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != X0
% 2.12/1.03      | sK3 != X1
% 2.12/1.03      | sK4 != sK4
% 2.12/1.03      | o_0_0_xboole_0 = X1 ),
% 2.12/1.03      inference(resolution_lifted,[status(thm)],[c_35,c_606]) ).
% 2.12/1.03  
% 2.12/1.03  cnf(c_1184,plain,
% 2.12/1.03      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))
% 2.12/1.03      | ~ r2_hidden(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 2.12/1.03      | r2_hidden(k1_funct_1(sK4,X0),sK3)
% 2.12/1.03      | o_0_0_xboole_0 = sK3 ),
% 2.12/1.03      inference(unflattening,[status(thm)],[c_1183]) ).
% 2.12/1.03  
% 2.12/1.03  cnf(c_1188,plain,
% 2.12/1.03      ( r2_hidden(k1_funct_1(sK4,X0),sK3)
% 2.12/1.03      | ~ r2_hidden(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
% 2.12/1.03      inference(global_propositional_subsumption,
% 2.12/1.03                [status(thm)],
% 2.12/1.03                [c_1184,c_34,c_33]) ).
% 2.12/1.03  
% 2.12/1.03  cnf(c_1189,plain,
% 2.12/1.03      ( ~ r2_hidden(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 2.12/1.03      | r2_hidden(k1_funct_1(sK4,X0),sK3) ),
% 2.12/1.03      inference(renaming,[status(thm)],[c_1188]) ).
% 2.12/1.03  
% 2.12/1.03  cnf(c_2388,plain,
% 2.12/1.03      ( r2_hidden(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top
% 2.12/1.03      | r2_hidden(k1_funct_1(sK4,X0),sK3) = iProver_top ),
% 2.12/1.03      inference(predicate_to_equality,[status(thm)],[c_1189]) ).
% 2.12/1.03  
% 2.12/1.03  cnf(c_4232,plain,
% 2.12/1.03      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.12/1.03      | r2_hidden(k1_funct_1(sK4,X0),sK3) = iProver_top ),
% 2.12/1.03      inference(demodulation,[status(thm)],[c_4226,c_2388]) ).
% 2.12/1.03  
% 2.12/1.03  cnf(c_32,negated_conjecture,
% 2.12/1.03      ( ~ r2_hidden(k1_funct_1(sK4,sK2),sK3) ),
% 2.12/1.03      inference(cnf_transformation,[],[f115]) ).
% 2.12/1.03  
% 2.12/1.03  cnf(c_2404,plain,
% 2.12/1.03      ( r2_hidden(k1_funct_1(sK4,sK2),sK3) != iProver_top ),
% 2.12/1.03      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.12/1.03  
% 2.12/1.03  cnf(c_5112,plain,
% 2.12/1.03      ( r2_hidden(sK2,k1_relat_1(sK4)) != iProver_top ),
% 2.12/1.03      inference(superposition,[status(thm)],[c_4232,c_2404]) ).
% 2.12/1.03  
% 2.12/1.03  cnf(c_5116,plain,
% 2.12/1.03      ( k5_xboole_0(k1_relat_1(sK4),k1_setfam_1(k6_enumset1(k1_relat_1(sK4),k1_relat_1(sK4),k1_relat_1(sK4),k1_relat_1(sK4),k1_relat_1(sK4),k1_relat_1(sK4),k1_relat_1(sK4),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = k1_relat_1(sK4) ),
% 2.12/1.03      inference(superposition,[status(thm)],[c_2412,c_5112]) ).
% 2.12/1.03  
% 2.12/1.03  cnf(c_5121,plain,
% 2.12/1.03      ( k5_xboole_0(k1_relat_1(sK4),k1_setfam_1(k6_enumset1(k1_relat_1(sK4),k1_relat_1(sK4),k1_relat_1(sK4),k1_relat_1(sK4),k1_relat_1(sK4),k1_relat_1(sK4),k1_relat_1(sK4),k1_relat_1(sK4)))) = k1_relat_1(sK4) ),
% 2.12/1.03      inference(light_normalisation,[status(thm)],[c_5116,c_4226]) ).
% 2.12/1.03  
% 2.12/1.03  cnf(c_3,plain,
% 2.12/1.03      ( k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 2.12/1.03      inference(cnf_transformation,[],[f129]) ).
% 2.12/1.03  
% 2.12/1.03  cnf(c_4263,plain,
% 2.12/1.03      ( k1_setfam_1(k6_enumset1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_relat_1(sK4))) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 2.12/1.03      inference(superposition,[status(thm)],[c_4226,c_3]) ).
% 2.12/1.03  
% 2.12/1.03  cnf(c_4264,plain,
% 2.12/1.03      ( k1_setfam_1(k6_enumset1(k1_relat_1(sK4),k1_relat_1(sK4),k1_relat_1(sK4),k1_relat_1(sK4),k1_relat_1(sK4),k1_relat_1(sK4),k1_relat_1(sK4),k1_relat_1(sK4))) = k1_relat_1(sK4) ),
% 2.12/1.03      inference(light_normalisation,[status(thm)],[c_4263,c_4226]) ).
% 2.12/1.03  
% 2.12/1.03  cnf(c_5909,plain,
% 2.12/1.03      ( k5_xboole_0(k1_relat_1(sK4),k1_relat_1(sK4)) = k1_relat_1(sK4) ),
% 2.12/1.03      inference(light_normalisation,[status(thm)],[c_5121,c_4264]) ).
% 2.12/1.03  
% 2.12/1.03  cnf(c_2,plain,
% 2.12/1.03      ( k5_xboole_0(X0,X0) = o_0_0_xboole_0 ),
% 2.12/1.03      inference(cnf_transformation,[],[f128]) ).
% 2.12/1.03  
% 2.12/1.03  cnf(c_5910,plain,
% 2.12/1.03      ( k1_relat_1(sK4) = o_0_0_xboole_0 ),
% 2.12/1.03      inference(demodulation,[status(thm)],[c_5909,c_2]) ).
% 2.12/1.03  
% 2.12/1.03  cnf(c_20,plain,
% 2.12/1.03      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) != X0 ),
% 2.12/1.03      inference(cnf_transformation,[],[f134]) ).
% 2.12/1.03  
% 2.12/1.03  cnf(c_4262,plain,
% 2.12/1.03      ( k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k1_relat_1(sK4))) != sK2 ),
% 2.12/1.03      inference(superposition,[status(thm)],[c_4226,c_20]) ).
% 2.12/1.03  
% 2.12/1.03  cnf(c_5918,plain,
% 2.12/1.03      ( k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,o_0_0_xboole_0)) != sK2 ),
% 2.12/1.03      inference(demodulation,[status(thm)],[c_5910,c_4262]) ).
% 2.12/1.03  
% 2.12/1.03  cnf(c_1,plain,
% 2.12/1.03      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,o_0_0_xboole_0)) = X0 ),
% 2.12/1.03      inference(cnf_transformation,[],[f127]) ).
% 2.12/1.03  
% 2.12/1.03  cnf(c_5973,plain,
% 2.12/1.03      ( sK2 != sK2 ),
% 2.12/1.03      inference(demodulation,[status(thm)],[c_5918,c_1]) ).
% 2.12/1.03  
% 2.12/1.03  cnf(c_5974,plain,
% 2.12/1.03      ( $false ),
% 2.12/1.03      inference(equality_resolution_simp,[status(thm)],[c_5973]) ).
% 2.12/1.03  
% 2.12/1.03  
% 2.12/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.12/1.03  
% 2.12/1.03  ------                               Statistics
% 2.12/1.03  
% 2.12/1.03  ------ General
% 2.12/1.03  
% 2.12/1.03  abstr_ref_over_cycles:                  0
% 2.12/1.03  abstr_ref_under_cycles:                 0
% 2.12/1.03  gc_basic_clause_elim:                   0
% 2.12/1.03  forced_gc_time:                         0
% 2.12/1.03  parsing_time:                           0.015
% 2.12/1.03  unif_index_cands_time:                  0.
% 2.12/1.03  unif_index_add_time:                    0.
% 2.12/1.03  orderings_time:                         0.
% 2.12/1.03  out_proof_time:                         0.008
% 2.12/1.03  total_time:                             0.261
% 2.12/1.03  num_of_symbols:                         59
% 2.12/1.03  num_of_terms:                           5775
% 2.12/1.03  
% 2.12/1.03  ------ Preprocessing
% 2.12/1.03  
% 2.12/1.03  num_of_splits:                          1
% 2.12/1.03  num_of_split_atoms:                     1
% 2.12/1.03  num_of_reused_defs:                     0
% 2.12/1.03  num_eq_ax_congr_red:                    31
% 2.12/1.03  num_of_sem_filtered_clauses:            1
% 2.12/1.03  num_of_subtypes:                        0
% 2.12/1.03  monotx_restored_types:                  0
% 2.12/1.03  sat_num_of_epr_types:                   0
% 2.12/1.03  sat_num_of_non_cyclic_types:            0
% 2.12/1.03  sat_guarded_non_collapsed_types:        0
% 2.12/1.03  num_pure_diseq_elim:                    0
% 2.12/1.03  simp_replaced_by:                       0
% 2.12/1.03  res_preprocessed:                       170
% 2.12/1.03  prep_upred:                             0
% 2.12/1.03  prep_unflattend:                        75
% 2.12/1.03  smt_new_axioms:                         0
% 2.12/1.03  pred_elim_cands:                        5
% 2.12/1.03  pred_elim:                              3
% 2.12/1.03  pred_elim_cl:                           5
% 2.12/1.03  pred_elim_cycles:                       12
% 2.12/1.03  merged_defs:                            8
% 2.12/1.03  merged_defs_ncl:                        0
% 2.12/1.03  bin_hyper_res:                          8
% 2.12/1.03  prep_cycles:                            4
% 2.12/1.03  pred_elim_time:                         0.032
% 2.12/1.03  splitting_time:                         0.
% 2.12/1.03  sem_filter_time:                        0.
% 2.12/1.03  monotx_time:                            0.
% 2.12/1.03  subtype_inf_time:                       0.
% 2.12/1.03  
% 2.12/1.03  ------ Problem properties
% 2.12/1.03  
% 2.12/1.03  clauses:                                32
% 2.12/1.03  conjectures:                            3
% 2.12/1.03  epr:                                    3
% 2.12/1.03  horn:                                   26
% 2.12/1.03  ground:                                 9
% 2.12/1.03  unary:                                  10
% 2.12/1.03  binary:                                 8
% 2.12/1.03  lits:                                   73
% 2.12/1.03  lits_eq:                                21
% 2.12/1.03  fd_pure:                                0
% 2.12/1.03  fd_pseudo:                              0
% 2.12/1.03  fd_cond:                                2
% 2.12/1.03  fd_pseudo_cond:                         1
% 2.12/1.03  ac_symbols:                             0
% 2.12/1.03  
% 2.12/1.03  ------ Propositional Solver
% 2.12/1.03  
% 2.12/1.03  prop_solver_calls:                      26
% 2.12/1.03  prop_fast_solver_calls:                 1189
% 2.12/1.03  smt_solver_calls:                       0
% 2.12/1.03  smt_fast_solver_calls:                  0
% 2.12/1.03  prop_num_of_clauses:                    1878
% 2.12/1.03  prop_preprocess_simplified:             6883
% 2.12/1.03  prop_fo_subsumed:                       17
% 2.12/1.03  prop_solver_time:                       0.
% 2.12/1.03  smt_solver_time:                        0.
% 2.12/1.03  smt_fast_solver_time:                   0.
% 2.12/1.03  prop_fast_solver_time:                  0.
% 2.12/1.03  prop_unsat_core_time:                   0.
% 2.12/1.03  
% 2.12/1.03  ------ QBF
% 2.12/1.03  
% 2.12/1.03  qbf_q_res:                              0
% 2.12/1.03  qbf_num_tautologies:                    0
% 2.12/1.03  qbf_prep_cycles:                        0
% 2.12/1.03  
% 2.12/1.03  ------ BMC1
% 2.12/1.03  
% 2.12/1.03  bmc1_current_bound:                     -1
% 2.12/1.03  bmc1_last_solved_bound:                 -1
% 2.12/1.03  bmc1_unsat_core_size:                   -1
% 2.12/1.03  bmc1_unsat_core_parents_size:           -1
% 2.12/1.03  bmc1_merge_next_fun:                    0
% 2.12/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.12/1.03  
% 2.12/1.03  ------ Instantiation
% 2.12/1.03  
% 2.12/1.03  inst_num_of_clauses:                    547
% 2.12/1.03  inst_num_in_passive:                    161
% 2.12/1.03  inst_num_in_active:                     264
% 2.12/1.03  inst_num_in_unprocessed:                122
% 2.12/1.03  inst_num_of_loops:                      320
% 2.12/1.03  inst_num_of_learning_restarts:          0
% 2.12/1.03  inst_num_moves_active_passive:          54
% 2.12/1.03  inst_lit_activity:                      0
% 2.12/1.03  inst_lit_activity_moves:                0
% 2.12/1.03  inst_num_tautologies:                   0
% 2.12/1.03  inst_num_prop_implied:                  0
% 2.12/1.03  inst_num_existing_simplified:           0
% 2.12/1.03  inst_num_eq_res_simplified:             0
% 2.12/1.03  inst_num_child_elim:                    0
% 2.12/1.03  inst_num_of_dismatching_blockings:      225
% 2.12/1.03  inst_num_of_non_proper_insts:           412
% 2.12/1.03  inst_num_of_duplicates:                 0
% 2.12/1.03  inst_inst_num_from_inst_to_res:         0
% 2.12/1.03  inst_dismatching_checking_time:         0.
% 2.12/1.03  
% 2.12/1.03  ------ Resolution
% 2.12/1.03  
% 2.12/1.03  res_num_of_clauses:                     0
% 2.12/1.03  res_num_in_passive:                     0
% 2.12/1.03  res_num_in_active:                      0
% 2.12/1.03  res_num_of_loops:                       174
% 2.12/1.03  res_forward_subset_subsumed:            34
% 2.12/1.03  res_backward_subset_subsumed:           0
% 2.12/1.03  res_forward_subsumed:                   0
% 2.12/1.03  res_backward_subsumed:                  1
% 2.12/1.03  res_forward_subsumption_resolution:     0
% 2.12/1.03  res_backward_subsumption_resolution:    0
% 2.12/1.03  res_clause_to_clause_subsumption:       108
% 2.12/1.03  res_orphan_elimination:                 0
% 2.12/1.03  res_tautology_del:                      57
% 2.12/1.03  res_num_eq_res_simplified:              0
% 2.12/1.03  res_num_sel_changes:                    0
% 2.12/1.03  res_moves_from_active_to_pass:          0
% 2.12/1.03  
% 2.12/1.03  ------ Superposition
% 2.12/1.03  
% 2.12/1.03  sup_time_total:                         0.
% 2.12/1.03  sup_time_generating:                    0.
% 2.12/1.03  sup_time_sim_full:                      0.
% 2.12/1.03  sup_time_sim_immed:                     0.
% 2.12/1.03  
% 2.12/1.03  sup_num_of_clauses:                     52
% 2.12/1.03  sup_num_in_active:                      34
% 2.12/1.03  sup_num_in_passive:                     18
% 2.12/1.03  sup_num_of_loops:                       62
% 2.12/1.03  sup_fw_superposition:                   19
% 2.12/1.03  sup_bw_superposition:                   41
% 2.12/1.03  sup_immediate_simplified:               13
% 2.12/1.03  sup_given_eliminated:                   0
% 2.12/1.03  comparisons_done:                       0
% 2.12/1.03  comparisons_avoided:                    0
% 2.12/1.03  
% 2.12/1.03  ------ Simplifications
% 2.12/1.03  
% 2.12/1.03  
% 2.12/1.03  sim_fw_subset_subsumed:                 8
% 2.12/1.03  sim_bw_subset_subsumed:                 0
% 2.12/1.03  sim_fw_subsumed:                        0
% 2.12/1.03  sim_bw_subsumed:                        0
% 2.12/1.03  sim_fw_subsumption_res:                 0
% 2.12/1.03  sim_bw_subsumption_res:                 0
% 2.12/1.03  sim_tautology_del:                      3
% 2.12/1.03  sim_eq_tautology_del:                   2
% 2.12/1.03  sim_eq_res_simp:                        0
% 2.12/1.03  sim_fw_demodulated:                     4
% 2.12/1.03  sim_bw_demodulated:                     28
% 2.12/1.03  sim_light_normalised:                   5
% 2.12/1.03  sim_joinable_taut:                      0
% 2.12/1.03  sim_joinable_simp:                      0
% 2.12/1.03  sim_ac_normalised:                      0
% 2.12/1.03  sim_smt_subsumption:                    0
% 2.12/1.03  
%------------------------------------------------------------------------------
