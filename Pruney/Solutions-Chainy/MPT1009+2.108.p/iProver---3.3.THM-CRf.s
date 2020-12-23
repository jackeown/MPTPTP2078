%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:49 EST 2020

% Result     : Theorem 11.73s
% Output     : CNFRefutation 11.73s
% Verified   : 
% Statistics : Number of formulae       :  216 (1606 expanded)
%              Number of clauses        :  103 ( 288 expanded)
%              Number of leaves         :   31 ( 420 expanded)
%              Depth                    :   25
%              Number of atoms          :  575 (3144 expanded)
%              Number of equality atoms :  288 (1508 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f26,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f28,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(pure_predicate_removal,[],[f27])).

fof(f44,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f45,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f44])).

fof(f65,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
        & k1_xboole_0 != X1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k7_relset_1(k1_tarski(sK3),sK4,sK6,sK5),k1_tarski(k1_funct_1(sK6,sK3)))
      & k1_xboole_0 != sK4
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4)))
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK3),sK4,sK6,sK5),k1_tarski(k1_funct_1(sK6,sK3)))
    & k1_xboole_0 != sK4
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4)))
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f45,f65])).

fof(f115,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4))) ),
    inference(cnf_transformation,[],[f66])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f118,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f76,f77])).

fof(f119,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f75,f118])).

fof(f120,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f74,f119])).

fof(f121,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f73,f120])).

fof(f122,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f72,f121])).

fof(f123,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f71,f122])).

fof(f130,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4))) ),
    inference(definition_unfolding,[],[f115,f123])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f23])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f103,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f51])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f126,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f78,f123,f123])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f101,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f100,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f99,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f17,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f105,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f102,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f127,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f102,f123])).

fof(f114,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f66])).

fof(f117,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK3),sK4,sK6,sK5),k1_tarski(k1_funct_1(sK6,sK3))) ),
    inference(cnf_transformation,[],[f66])).

fof(f129,plain,(
    ~ r1_tarski(k7_relset_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4,sK6,sK5),k6_enumset1(k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3))) ),
    inference(definition_unfolding,[],[f117,f123,f123])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f112,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f106,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f12,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f46,plain,(
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

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(definition_folding,[],[f30,f47,f46])).

fof(f62,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) )
      & ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f97,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ),
    inference(cnf_transformation,[],[f62])).

fof(f145,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(equality_resolution,[],[f97])).

fof(f59,plain,(
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
    inference(nnf_transformation,[],[f46])).

fof(f60,plain,(
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
    inference(flattening,[],[f59])).

fof(f61,plain,(
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
    inference(rectify,[],[f60])).

fof(f96,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f61])).

fof(f137,plain,(
    ! [X6,X4,X2,X8,X7,X5,X3,X1] : sP0(X1,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(equality_resolution,[],[f96])).

fof(f55,plain,(
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
    inference(nnf_transformation,[],[f47])).

fof(f56,plain,(
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
    inference(rectify,[],[f55])).

fof(f57,plain,(
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

fof(f58,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f56,f57])).

fof(f85,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] :
      ( r2_hidden(X10,X8)
      | ~ sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f110,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f128,plain,(
    ! [X0,X1] :
      ( k6_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f110,f123])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f109,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f107,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f25,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f42])).

fof(f113,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f49])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f131,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f68])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f53])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f136,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f82])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f69,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f20,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f108,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_42,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4))) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_1530,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_37,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_1534,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_3854,plain,
    ( v4_relat_1(sK6,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1530,c_1534])).

cnf(c_30,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1540,plain,
    ( v4_relat_1(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f126])).

cnf(c_1560,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_8388,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_relat_1(X1)
    | k1_relat_1(X1) = k1_xboole_0
    | v4_relat_1(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1540,c_1560])).

cnf(c_30782,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_relat_1(sK6)
    | k1_relat_1(sK6) = k1_xboole_0
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3854,c_8388])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_25,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_263,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_25])).

cnf(c_264,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_263])).

cnf(c_337,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_27,c_264])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1978,plain,
    ( r1_tarski(sK6,k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) ),
    inference(resolution,[status(thm)],[c_26,c_42])).

cnf(c_2268,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4))
    | v1_relat_1(sK6) ),
    inference(resolution,[status(thm)],[c_337,c_1978])).

cnf(c_31,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_2273,plain,
    ( v1_relat_1(sK6) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2268,c_31])).

cnf(c_30815,plain,
    ( ~ v1_relat_1(sK6)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_relat_1(sK6)
    | k1_relat_1(sK6) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_30782])).

cnf(c_31753,plain,
    ( k1_relat_1(sK6) = k1_xboole_0
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_relat_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_30782,c_2273,c_30815])).

cnf(c_31754,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_relat_1(sK6)
    | k1_relat_1(sK6) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_31753])).

cnf(c_1539,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_28,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_1542,plain,
    ( k9_relat_1(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k11_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_6598,plain,
    ( k9_relat_1(k2_zfmisc_1(X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) = k11_relat_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_1539,c_1542])).

cnf(c_31775,plain,
    ( k9_relat_1(k2_zfmisc_1(X0,X1),k1_relat_1(sK6)) = k11_relat_1(k2_zfmisc_1(X0,X1),sK3)
    | k1_relat_1(sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_31754,c_6598])).

cnf(c_43,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_44,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_40,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4,sK6,sK5),k6_enumset1(k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3))) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_38,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1950,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)))
    | k7_relset_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4,sK6,X0) = k9_relat_1(sK6,X0) ),
    inference(instantiation,[status(thm)],[c_38])).

cnf(c_2123,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)))
    | k7_relset_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4,sK6,sK5) = k9_relat_1(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_1950])).

cnf(c_2274,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2273])).

cnf(c_32,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_12423,plain,
    ( r1_tarski(k9_relat_1(sK6,X0),k2_relat_1(sK6))
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_31558,plain,
    ( r1_tarski(k9_relat_1(sK6,sK5),k2_relat_1(sK6))
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_12423])).

cnf(c_687,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1938,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k7_relset_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4,sK6,sK5),k6_enumset1(k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3)))
    | k6_enumset1(k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3)) != X1
    | k7_relset_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4,sK6,sK5) != X0 ),
    inference(instantiation,[status(thm)],[c_687])).

cnf(c_2122,plain,
    ( r1_tarski(k7_relset_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4,sK6,sK5),k6_enumset1(k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3)))
    | ~ r1_tarski(k9_relat_1(sK6,sK5),X0)
    | k6_enumset1(k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3)) != X0
    | k7_relset_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4,sK6,sK5) != k9_relat_1(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_1938])).

cnf(c_31563,plain,
    ( r1_tarski(k7_relset_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4,sK6,sK5),k6_enumset1(k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3)))
    | ~ r1_tarski(k9_relat_1(sK6,sK5),k2_relat_1(sK6))
    | k6_enumset1(k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3)) != k2_relat_1(sK6)
    | k7_relset_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4,sK6,sK5) != k9_relat_1(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_2122])).

cnf(c_24,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f145])).

cnf(c_1545,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_14,plain,
    ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f137])).

cnf(c_1555,plain,
    ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_12,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    | ~ sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9)
    | r2_hidden(X0,X9) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1557,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) != iProver_top
    | sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9) != iProver_top
    | r2_hidden(X0,X9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_9568,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != iProver_top
    | r2_hidden(X7,X8) = iProver_top ),
    inference(superposition,[status(thm)],[c_1555,c_1557])).

cnf(c_21401,plain,
    ( r2_hidden(X0,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1545,c_9568])).

cnf(c_31776,plain,
    ( k1_relat_1(sK6) = k1_xboole_0
    | r2_hidden(sK3,k1_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_31754,c_21401])).

cnf(c_36,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k6_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_1535,plain,
    ( k6_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k11_relat_1(X0,X1)
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_32692,plain,
    ( k6_enumset1(k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3)) = k11_relat_1(sK6,sK3)
    | k1_relat_1(sK6) = k1_xboole_0
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_31776,c_1535])).

cnf(c_1543,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2976,plain,
    ( r1_tarski(sK6,k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1530,c_1543])).

cnf(c_1528,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_337])).

cnf(c_2980,plain,
    ( v1_relat_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2976,c_1528])).

cnf(c_3399,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2980,c_2274])).

cnf(c_6599,plain,
    ( k9_relat_1(sK6,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k11_relat_1(sK6,X0) ),
    inference(superposition,[status(thm)],[c_3399,c_1542])).

cnf(c_35,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1536,plain,
    ( k7_relat_1(X0,X1) = X0
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_4823,plain,
    ( k7_relat_1(sK6,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = sK6
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3854,c_1536])).

cnf(c_1895,plain,
    ( v4_relat_1(sK6,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4))) ),
    inference(instantiation,[status(thm)],[c_37])).

cnf(c_2045,plain,
    ( ~ v4_relat_1(sK6,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))
    | ~ v1_relat_1(sK6)
    | k7_relat_1(sK6,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = sK6 ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_5556,plain,
    ( k7_relat_1(sK6,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4823,c_42,c_1895,c_2045,c_2273])).

cnf(c_33,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1537,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_3932,plain,
    ( k2_relat_1(k7_relat_1(sK6,X0)) = k9_relat_1(sK6,X0) ),
    inference(superposition,[status(thm)],[c_3399,c_1537])).

cnf(c_5562,plain,
    ( k9_relat_1(sK6,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = k2_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_5556,c_3932])).

cnf(c_6634,plain,
    ( k11_relat_1(sK6,sK3) = k2_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_6599,c_5562])).

cnf(c_32693,plain,
    ( k6_enumset1(k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3)) = k2_relat_1(sK6)
    | k1_relat_1(sK6) = k1_xboole_0
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_32692,c_6634])).

cnf(c_32695,plain,
    ( k1_relat_1(sK6) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_31775,c_44,c_42,c_40,c_2123,c_2273,c_2274,c_31558,c_31563,c_32693])).

cnf(c_31774,plain,
    ( k1_relat_1(sK6) = k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_31754,c_1530])).

cnf(c_45,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_39,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_1923,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X2)))
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_39])).

cnf(c_2995,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)))
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK4)))
    | ~ r1_tarski(k1_relat_1(sK6),k1_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_1923])).

cnf(c_2996,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK4))) = iProver_top
    | r1_tarski(k1_relat_1(sK6),k1_relat_1(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2995])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_1924,plain,
    ( r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3189,plain,
    ( r1_tarski(k1_relat_1(sK6),k1_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_1924])).

cnf(c_3190,plain,
    ( r1_tarski(k1_relat_1(sK6),k1_relat_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3189])).

cnf(c_31872,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_31774,c_45,c_2996,c_3190])).

cnf(c_31877,plain,
    ( r1_tarski(sK6,k2_zfmisc_1(k1_relat_1(sK6),sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_31872,c_1543])).

cnf(c_32699,plain,
    ( r1_tarski(sK6,k2_zfmisc_1(k1_xboole_0,sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_32695,c_31877])).

cnf(c_8,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f136])).

cnf(c_32785,plain,
    ( r1_tarski(sK6,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_32699,c_8])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1563,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1565,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4775,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1563,c_1565])).

cnf(c_33849,plain,
    ( sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_32785,c_4775])).

cnf(c_1533,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_5013,plain,
    ( k7_relset_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4,sK6,X0) = k9_relat_1(sK6,X0) ),
    inference(superposition,[status(thm)],[c_1530,c_1533])).

cnf(c_1531,plain,
    ( r1_tarski(k7_relset_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4,sK6,sK5),k6_enumset1(k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_5277,plain,
    ( r1_tarski(k9_relat_1(sK6,sK5),k6_enumset1(k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5013,c_1531])).

cnf(c_35426,plain,
    ( r1_tarski(k9_relat_1(k1_xboole_0,sK5),k6_enumset1(k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_33849,c_5277])).

cnf(c_34,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_35458,plain,
    ( r1_tarski(k1_xboole_0,k6_enumset1(k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_35426,c_34])).

cnf(c_35600,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_35458,c_1563])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:42:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.73/2.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.73/2.00  
% 11.73/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.73/2.00  
% 11.73/2.00  ------  iProver source info
% 11.73/2.00  
% 11.73/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.73/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.73/2.00  git: non_committed_changes: false
% 11.73/2.00  git: last_make_outside_of_git: false
% 11.73/2.00  
% 11.73/2.00  ------ 
% 11.73/2.00  ------ Parsing...
% 11.73/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.73/2.00  
% 11.73/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 11.73/2.00  
% 11.73/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.73/2.00  
% 11.73/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.73/2.00  ------ Proving...
% 11.73/2.00  ------ Problem Properties 
% 11.73/2.00  
% 11.73/2.00  
% 11.73/2.00  clauses                                 43
% 11.73/2.00  conjectures                             4
% 11.73/2.00  EPR                                     17
% 11.73/2.00  Horn                                    39
% 11.73/2.00  unary                                   21
% 11.73/2.00  binary                                  8
% 11.73/2.00  lits                                    86
% 11.73/2.00  lits eq                                 24
% 11.73/2.00  fd_pure                                 0
% 11.73/2.00  fd_pseudo                               0
% 11.73/2.00  fd_cond                                 1
% 11.73/2.00  fd_pseudo_cond                          4
% 11.73/2.00  AC symbols                              0
% 11.73/2.00  
% 11.73/2.00  ------ Input Options Time Limit: Unbounded
% 11.73/2.00  
% 11.73/2.00  
% 11.73/2.00  ------ 
% 11.73/2.00  Current options:
% 11.73/2.00  ------ 
% 11.73/2.00  
% 11.73/2.00  
% 11.73/2.00  
% 11.73/2.00  
% 11.73/2.00  ------ Proving...
% 11.73/2.00  
% 11.73/2.00  
% 11.73/2.00  % SZS status Theorem for theBenchmark.p
% 11.73/2.00  
% 11.73/2.00   Resolution empty clause
% 11.73/2.00  
% 11.73/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.73/2.00  
% 11.73/2.00  fof(f26,conjecture,(
% 11.73/2.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 11.73/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/2.00  
% 11.73/2.00  fof(f27,negated_conjecture,(
% 11.73/2.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 11.73/2.00    inference(negated_conjecture,[],[f26])).
% 11.73/2.00  
% 11.73/2.00  fof(f28,plain,(
% 11.73/2.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 11.73/2.00    inference(pure_predicate_removal,[],[f27])).
% 11.73/2.00  
% 11.73/2.00  fof(f44,plain,(
% 11.73/2.00    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 11.73/2.00    inference(ennf_transformation,[],[f28])).
% 11.73/2.00  
% 11.73/2.00  fof(f45,plain,(
% 11.73/2.00    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 11.73/2.00    inference(flattening,[],[f44])).
% 11.73/2.00  
% 11.73/2.00  fof(f65,plain,(
% 11.73/2.00    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK3),sK4,sK6,sK5),k1_tarski(k1_funct_1(sK6,sK3))) & k1_xboole_0 != sK4 & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4))) & v1_funct_1(sK6))),
% 11.73/2.00    introduced(choice_axiom,[])).
% 11.73/2.00  
% 11.73/2.00  fof(f66,plain,(
% 11.73/2.00    ~r1_tarski(k7_relset_1(k1_tarski(sK3),sK4,sK6,sK5),k1_tarski(k1_funct_1(sK6,sK3))) & k1_xboole_0 != sK4 & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4))) & v1_funct_1(sK6)),
% 11.73/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f45,f65])).
% 11.73/2.00  
% 11.73/2.00  fof(f115,plain,(
% 11.73/2.00    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4)))),
% 11.73/2.00    inference(cnf_transformation,[],[f66])).
% 11.73/2.00  
% 11.73/2.00  fof(f3,axiom,(
% 11.73/2.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 11.73/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/2.00  
% 11.73/2.00  fof(f71,plain,(
% 11.73/2.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 11.73/2.00    inference(cnf_transformation,[],[f3])).
% 11.73/2.00  
% 11.73/2.00  fof(f4,axiom,(
% 11.73/2.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 11.73/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/2.00  
% 11.73/2.00  fof(f72,plain,(
% 11.73/2.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 11.73/2.00    inference(cnf_transformation,[],[f4])).
% 11.73/2.00  
% 11.73/2.00  fof(f5,axiom,(
% 11.73/2.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 11.73/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/2.00  
% 11.73/2.00  fof(f73,plain,(
% 11.73/2.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 11.73/2.00    inference(cnf_transformation,[],[f5])).
% 11.73/2.00  
% 11.73/2.00  fof(f6,axiom,(
% 11.73/2.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 11.73/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/2.00  
% 11.73/2.00  fof(f74,plain,(
% 11.73/2.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 11.73/2.00    inference(cnf_transformation,[],[f6])).
% 11.73/2.00  
% 11.73/2.00  fof(f7,axiom,(
% 11.73/2.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 11.73/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/2.00  
% 11.73/2.00  fof(f75,plain,(
% 11.73/2.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 11.73/2.00    inference(cnf_transformation,[],[f7])).
% 11.73/2.00  
% 11.73/2.00  fof(f8,axiom,(
% 11.73/2.00    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 11.73/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/2.00  
% 11.73/2.00  fof(f76,plain,(
% 11.73/2.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 11.73/2.00    inference(cnf_transformation,[],[f8])).
% 11.73/2.00  
% 11.73/2.00  fof(f9,axiom,(
% 11.73/2.00    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 11.73/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/2.00  
% 11.73/2.00  fof(f77,plain,(
% 11.73/2.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 11.73/2.00    inference(cnf_transformation,[],[f9])).
% 11.73/2.00  
% 11.73/2.00  fof(f118,plain,(
% 11.73/2.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 11.73/2.00    inference(definition_unfolding,[],[f76,f77])).
% 11.73/2.00  
% 11.73/2.00  fof(f119,plain,(
% 11.73/2.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 11.73/2.00    inference(definition_unfolding,[],[f75,f118])).
% 11.73/2.00  
% 11.73/2.00  fof(f120,plain,(
% 11.73/2.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 11.73/2.00    inference(definition_unfolding,[],[f74,f119])).
% 11.73/2.00  
% 11.73/2.00  fof(f121,plain,(
% 11.73/2.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 11.73/2.00    inference(definition_unfolding,[],[f73,f120])).
% 11.73/2.00  
% 11.73/2.00  fof(f122,plain,(
% 11.73/2.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 11.73/2.00    inference(definition_unfolding,[],[f72,f121])).
% 11.73/2.00  
% 11.73/2.00  fof(f123,plain,(
% 11.73/2.00    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 11.73/2.00    inference(definition_unfolding,[],[f71,f122])).
% 11.73/2.00  
% 11.73/2.00  fof(f130,plain,(
% 11.73/2.00    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)))),
% 11.73/2.00    inference(definition_unfolding,[],[f115,f123])).
% 11.73/2.00  
% 11.73/2.00  fof(f23,axiom,(
% 11.73/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 11.73/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/2.00  
% 11.73/2.00  fof(f29,plain,(
% 11.73/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 11.73/2.00    inference(pure_predicate_removal,[],[f23])).
% 11.73/2.00  
% 11.73/2.00  fof(f40,plain,(
% 11.73/2.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.73/2.00    inference(ennf_transformation,[],[f29])).
% 11.73/2.00  
% 11.73/2.00  fof(f111,plain,(
% 11.73/2.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.73/2.00    inference(cnf_transformation,[],[f40])).
% 11.73/2.00  
% 11.73/2.00  fof(f16,axiom,(
% 11.73/2.00    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 11.73/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/2.00  
% 11.73/2.00  fof(f33,plain,(
% 11.73/2.00    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.73/2.00    inference(ennf_transformation,[],[f16])).
% 11.73/2.00  
% 11.73/2.00  fof(f64,plain,(
% 11.73/2.00    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 11.73/2.00    inference(nnf_transformation,[],[f33])).
% 11.73/2.00  
% 11.73/2.00  fof(f103,plain,(
% 11.73/2.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.73/2.00    inference(cnf_transformation,[],[f64])).
% 11.73/2.00  
% 11.73/2.00  fof(f10,axiom,(
% 11.73/2.00    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 11.73/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/2.00  
% 11.73/2.00  fof(f51,plain,(
% 11.73/2.00    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 11.73/2.00    inference(nnf_transformation,[],[f10])).
% 11.73/2.00  
% 11.73/2.00  fof(f52,plain,(
% 11.73/2.00    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 11.73/2.00    inference(flattening,[],[f51])).
% 11.73/2.00  
% 11.73/2.00  fof(f78,plain,(
% 11.73/2.00    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 11.73/2.00    inference(cnf_transformation,[],[f52])).
% 11.73/2.00  
% 11.73/2.00  fof(f126,plain,(
% 11.73/2.00    ( ! [X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 11.73/2.00    inference(definition_unfolding,[],[f78,f123,f123])).
% 11.73/2.00  
% 11.73/2.00  fof(f14,axiom,(
% 11.73/2.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 11.73/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/2.00  
% 11.73/2.00  fof(f31,plain,(
% 11.73/2.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 11.73/2.00    inference(ennf_transformation,[],[f14])).
% 11.73/2.00  
% 11.73/2.00  fof(f101,plain,(
% 11.73/2.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 11.73/2.00    inference(cnf_transformation,[],[f31])).
% 11.73/2.00  
% 11.73/2.00  fof(f13,axiom,(
% 11.73/2.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 11.73/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/2.00  
% 11.73/2.00  fof(f63,plain,(
% 11.73/2.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 11.73/2.00    inference(nnf_transformation,[],[f13])).
% 11.73/2.00  
% 11.73/2.00  fof(f100,plain,(
% 11.73/2.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 11.73/2.00    inference(cnf_transformation,[],[f63])).
% 11.73/2.00  
% 11.73/2.00  fof(f99,plain,(
% 11.73/2.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 11.73/2.00    inference(cnf_transformation,[],[f63])).
% 11.73/2.00  
% 11.73/2.00  fof(f17,axiom,(
% 11.73/2.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 11.73/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/2.00  
% 11.73/2.00  fof(f105,plain,(
% 11.73/2.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 11.73/2.00    inference(cnf_transformation,[],[f17])).
% 11.73/2.00  
% 11.73/2.00  fof(f15,axiom,(
% 11.73/2.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 11.73/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/2.00  
% 11.73/2.00  fof(f32,plain,(
% 11.73/2.00    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 11.73/2.00    inference(ennf_transformation,[],[f15])).
% 11.73/2.00  
% 11.73/2.00  fof(f102,plain,(
% 11.73/2.00    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 11.73/2.00    inference(cnf_transformation,[],[f32])).
% 11.73/2.00  
% 11.73/2.00  fof(f127,plain,(
% 11.73/2.00    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 11.73/2.00    inference(definition_unfolding,[],[f102,f123])).
% 11.73/2.00  
% 11.73/2.00  fof(f114,plain,(
% 11.73/2.00    v1_funct_1(sK6)),
% 11.73/2.00    inference(cnf_transformation,[],[f66])).
% 11.73/2.00  
% 11.73/2.00  fof(f117,plain,(
% 11.73/2.00    ~r1_tarski(k7_relset_1(k1_tarski(sK3),sK4,sK6,sK5),k1_tarski(k1_funct_1(sK6,sK3)))),
% 11.73/2.00    inference(cnf_transformation,[],[f66])).
% 11.73/2.00  
% 11.73/2.00  fof(f129,plain,(
% 11.73/2.00    ~r1_tarski(k7_relset_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4,sK6,sK5),k6_enumset1(k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3)))),
% 11.73/2.00    inference(definition_unfolding,[],[f117,f123,f123])).
% 11.73/2.00  
% 11.73/2.00  fof(f24,axiom,(
% 11.73/2.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 11.73/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/2.00  
% 11.73/2.00  fof(f41,plain,(
% 11.73/2.00    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.73/2.00    inference(ennf_transformation,[],[f24])).
% 11.73/2.00  
% 11.73/2.00  fof(f112,plain,(
% 11.73/2.00    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.73/2.00    inference(cnf_transformation,[],[f41])).
% 11.73/2.00  
% 11.73/2.00  fof(f18,axiom,(
% 11.73/2.00    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 11.73/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/2.00  
% 11.73/2.00  fof(f34,plain,(
% 11.73/2.00    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 11.73/2.00    inference(ennf_transformation,[],[f18])).
% 11.73/2.00  
% 11.73/2.00  fof(f106,plain,(
% 11.73/2.00    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 11.73/2.00    inference(cnf_transformation,[],[f34])).
% 11.73/2.00  
% 11.73/2.00  fof(f12,axiom,(
% 11.73/2.00    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> ~(X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)))),
% 11.73/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/2.00  
% 11.73/2.00  fof(f30,plain,(
% 11.73/2.00    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9)))),
% 11.73/2.00    inference(ennf_transformation,[],[f12])).
% 11.73/2.00  
% 11.73/2.00  fof(f47,plain,(
% 11.73/2.00    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) <=> ! [X9] : (r2_hidden(X9,X8) <=> sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 11.73/2.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 11.73/2.00  
% 11.73/2.00  fof(f46,plain,(
% 11.73/2.00    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9))),
% 11.73/2.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 11.73/2.00  
% 11.73/2.00  fof(f48,plain,(
% 11.73/2.00    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8))),
% 11.73/2.00    inference(definition_folding,[],[f30,f47,f46])).
% 11.73/2.00  
% 11.73/2.00  fof(f62,plain,(
% 11.73/2.00    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) & (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8))),
% 11.73/2.00    inference(nnf_transformation,[],[f48])).
% 11.73/2.00  
% 11.73/2.00  fof(f97,plain,(
% 11.73/2.00    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8) )),
% 11.73/2.00    inference(cnf_transformation,[],[f62])).
% 11.73/2.00  
% 11.73/2.00  fof(f145,plain,(
% 11.73/2.00    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))) )),
% 11.73/2.00    inference(equality_resolution,[],[f97])).
% 11.73/2.00  
% 11.73/2.00  fof(f59,plain,(
% 11.73/2.00    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & ((X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9) | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 11.73/2.00    inference(nnf_transformation,[],[f46])).
% 11.73/2.00  
% 11.73/2.00  fof(f60,plain,(
% 11.73/2.00    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 11.73/2.00    inference(flattening,[],[f59])).
% 11.73/2.00  
% 11.73/2.00  fof(f61,plain,(
% 11.73/2.00    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4 & X0 != X5 & X0 != X6 & X0 != X7 & X0 != X8)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | X0 = X8 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 11.73/2.00    inference(rectify,[],[f60])).
% 11.73/2.00  
% 11.73/2.00  fof(f96,plain,(
% 11.73/2.00    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | X0 != X1) )),
% 11.73/2.00    inference(cnf_transformation,[],[f61])).
% 11.73/2.00  
% 11.73/2.00  fof(f137,plain,(
% 11.73/2.00    ( ! [X6,X4,X2,X8,X7,X5,X3,X1] : (sP0(X1,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 11.73/2.00    inference(equality_resolution,[],[f96])).
% 11.73/2.00  
% 11.73/2.00  fof(f55,plain,(
% 11.73/2.00    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8)))) & (! [X9] : ((r2_hidden(X9,X8) | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 11.73/2.00    inference(nnf_transformation,[],[f47])).
% 11.73/2.00  
% 11.73/2.00  fof(f56,plain,(
% 11.73/2.00    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8)))) & (! [X10] : ((r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 11.73/2.00    inference(rectify,[],[f55])).
% 11.73/2.00  
% 11.73/2.00  fof(f57,plain,(
% 11.73/2.00    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] : (? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8))) => ((~sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8))))),
% 11.73/2.00    introduced(choice_axiom,[])).
% 11.73/2.00  
% 11.73/2.00  fof(f58,plain,(
% 11.73/2.00    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ((~sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)))) & (! [X10] : ((r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 11.73/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f56,f57])).
% 11.73/2.00  
% 11.73/2.00  fof(f85,plain,(
% 11.73/2.00    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] : (r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 11.73/2.00    inference(cnf_transformation,[],[f58])).
% 11.73/2.00  
% 11.73/2.00  fof(f22,axiom,(
% 11.73/2.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)))),
% 11.73/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/2.00  
% 11.73/2.00  fof(f38,plain,(
% 11.73/2.00    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 11.73/2.00    inference(ennf_transformation,[],[f22])).
% 11.73/2.00  
% 11.73/2.00  fof(f39,plain,(
% 11.73/2.00    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 11.73/2.00    inference(flattening,[],[f38])).
% 11.73/2.00  
% 11.73/2.00  fof(f110,plain,(
% 11.73/2.00    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 11.73/2.00    inference(cnf_transformation,[],[f39])).
% 11.73/2.00  
% 11.73/2.00  fof(f128,plain,(
% 11.73/2.00    ( ! [X0,X1] : (k6_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 11.73/2.00    inference(definition_unfolding,[],[f110,f123])).
% 11.73/2.00  
% 11.73/2.00  fof(f21,axiom,(
% 11.73/2.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 11.73/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/2.00  
% 11.73/2.00  fof(f36,plain,(
% 11.73/2.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 11.73/2.00    inference(ennf_transformation,[],[f21])).
% 11.73/2.00  
% 11.73/2.00  fof(f37,plain,(
% 11.73/2.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 11.73/2.00    inference(flattening,[],[f36])).
% 11.73/2.00  
% 11.73/2.00  fof(f109,plain,(
% 11.73/2.00    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.73/2.00    inference(cnf_transformation,[],[f37])).
% 11.73/2.00  
% 11.73/2.00  fof(f19,axiom,(
% 11.73/2.00    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 11.73/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/2.00  
% 11.73/2.00  fof(f35,plain,(
% 11.73/2.00    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 11.73/2.00    inference(ennf_transformation,[],[f19])).
% 11.73/2.00  
% 11.73/2.00  fof(f107,plain,(
% 11.73/2.00    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 11.73/2.00    inference(cnf_transformation,[],[f35])).
% 11.73/2.00  
% 11.73/2.00  fof(f25,axiom,(
% 11.73/2.00    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 11.73/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/2.00  
% 11.73/2.00  fof(f42,plain,(
% 11.73/2.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 11.73/2.00    inference(ennf_transformation,[],[f25])).
% 11.73/2.00  
% 11.73/2.00  fof(f43,plain,(
% 11.73/2.00    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 11.73/2.00    inference(flattening,[],[f42])).
% 11.73/2.00  
% 11.73/2.00  fof(f113,plain,(
% 11.73/2.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 11.73/2.00    inference(cnf_transformation,[],[f43])).
% 11.73/2.00  
% 11.73/2.00  fof(f1,axiom,(
% 11.73/2.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.73/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/2.00  
% 11.73/2.00  fof(f49,plain,(
% 11.73/2.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.73/2.00    inference(nnf_transformation,[],[f1])).
% 11.73/2.00  
% 11.73/2.00  fof(f50,plain,(
% 11.73/2.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.73/2.00    inference(flattening,[],[f49])).
% 11.73/2.00  
% 11.73/2.00  fof(f68,plain,(
% 11.73/2.00    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 11.73/2.00    inference(cnf_transformation,[],[f50])).
% 11.73/2.00  
% 11.73/2.00  fof(f131,plain,(
% 11.73/2.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.73/2.00    inference(equality_resolution,[],[f68])).
% 11.73/2.00  
% 11.73/2.00  fof(f11,axiom,(
% 11.73/2.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 11.73/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/2.00  
% 11.73/2.00  fof(f53,plain,(
% 11.73/2.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 11.73/2.00    inference(nnf_transformation,[],[f11])).
% 11.73/2.00  
% 11.73/2.00  fof(f54,plain,(
% 11.73/2.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 11.73/2.00    inference(flattening,[],[f53])).
% 11.73/2.00  
% 11.73/2.00  fof(f82,plain,(
% 11.73/2.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 11.73/2.00    inference(cnf_transformation,[],[f54])).
% 11.73/2.00  
% 11.73/2.00  fof(f136,plain,(
% 11.73/2.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 11.73/2.00    inference(equality_resolution,[],[f82])).
% 11.73/2.00  
% 11.73/2.00  fof(f2,axiom,(
% 11.73/2.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 11.73/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/2.00  
% 11.73/2.00  fof(f70,plain,(
% 11.73/2.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 11.73/2.00    inference(cnf_transformation,[],[f2])).
% 11.73/2.00  
% 11.73/2.00  fof(f69,plain,(
% 11.73/2.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.73/2.00    inference(cnf_transformation,[],[f50])).
% 11.73/2.00  
% 11.73/2.00  fof(f20,axiom,(
% 11.73/2.00    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 11.73/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/2.00  
% 11.73/2.00  fof(f108,plain,(
% 11.73/2.00    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 11.73/2.00    inference(cnf_transformation,[],[f20])).
% 11.73/2.00  
% 11.73/2.00  cnf(c_42,negated_conjecture,
% 11.73/2.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4))) ),
% 11.73/2.00      inference(cnf_transformation,[],[f130]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_1530,plain,
% 11.73/2.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4))) = iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_37,plain,
% 11.73/2.00      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 11.73/2.00      inference(cnf_transformation,[],[f111]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_1534,plain,
% 11.73/2.00      ( v4_relat_1(X0,X1) = iProver_top
% 11.73/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_3854,plain,
% 11.73/2.00      ( v4_relat_1(sK6,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_1530,c_1534]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_30,plain,
% 11.73/2.00      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 11.73/2.00      inference(cnf_transformation,[],[f103]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_1540,plain,
% 11.73/2.00      ( v4_relat_1(X0,X1) != iProver_top
% 11.73/2.00      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 11.73/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_6,plain,
% 11.73/2.00      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
% 11.73/2.00      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
% 11.73/2.00      | k1_xboole_0 = X0 ),
% 11.73/2.00      inference(cnf_transformation,[],[f126]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_1560,plain,
% 11.73/2.00      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
% 11.73/2.00      | k1_xboole_0 = X1
% 11.73/2.00      | r1_tarski(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_8388,plain,
% 11.73/2.00      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_relat_1(X1)
% 11.73/2.00      | k1_relat_1(X1) = k1_xboole_0
% 11.73/2.00      | v4_relat_1(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top
% 11.73/2.00      | v1_relat_1(X1) != iProver_top ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_1540,c_1560]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_30782,plain,
% 11.73/2.00      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_relat_1(sK6)
% 11.73/2.00      | k1_relat_1(sK6) = k1_xboole_0
% 11.73/2.00      | v1_relat_1(sK6) != iProver_top ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_3854,c_8388]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_27,plain,
% 11.73/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 11.73/2.00      inference(cnf_transformation,[],[f101]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_25,plain,
% 11.73/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.73/2.00      inference(cnf_transformation,[],[f100]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_263,plain,
% 11.73/2.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 11.73/2.00      inference(prop_impl,[status(thm)],[c_25]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_264,plain,
% 11.73/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.73/2.00      inference(renaming,[status(thm)],[c_263]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_337,plain,
% 11.73/2.00      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 11.73/2.00      inference(bin_hyper_res,[status(thm)],[c_27,c_264]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_26,plain,
% 11.73/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 11.73/2.00      inference(cnf_transformation,[],[f99]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_1978,plain,
% 11.73/2.00      ( r1_tarski(sK6,k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) ),
% 11.73/2.00      inference(resolution,[status(thm)],[c_26,c_42]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_2268,plain,
% 11.73/2.00      ( ~ v1_relat_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4))
% 11.73/2.00      | v1_relat_1(sK6) ),
% 11.73/2.00      inference(resolution,[status(thm)],[c_337,c_1978]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_31,plain,
% 11.73/2.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 11.73/2.00      inference(cnf_transformation,[],[f105]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_2273,plain,
% 11.73/2.00      ( v1_relat_1(sK6) ),
% 11.73/2.00      inference(forward_subsumption_resolution,[status(thm)],[c_2268,c_31]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_30815,plain,
% 11.73/2.00      ( ~ v1_relat_1(sK6)
% 11.73/2.00      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_relat_1(sK6)
% 11.73/2.00      | k1_relat_1(sK6) = k1_xboole_0 ),
% 11.73/2.00      inference(predicate_to_equality_rev,[status(thm)],[c_30782]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_31753,plain,
% 11.73/2.00      ( k1_relat_1(sK6) = k1_xboole_0
% 11.73/2.00      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_relat_1(sK6) ),
% 11.73/2.00      inference(global_propositional_subsumption,
% 11.73/2.00                [status(thm)],
% 11.73/2.00                [c_30782,c_2273,c_30815]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_31754,plain,
% 11.73/2.00      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_relat_1(sK6)
% 11.73/2.00      | k1_relat_1(sK6) = k1_xboole_0 ),
% 11.73/2.00      inference(renaming,[status(thm)],[c_31753]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_1539,plain,
% 11.73/2.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_28,plain,
% 11.73/2.00      ( ~ v1_relat_1(X0)
% 11.73/2.00      | k9_relat_1(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
% 11.73/2.00      inference(cnf_transformation,[],[f127]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_1542,plain,
% 11.73/2.00      ( k9_relat_1(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k11_relat_1(X0,X1)
% 11.73/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_6598,plain,
% 11.73/2.00      ( k9_relat_1(k2_zfmisc_1(X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) = k11_relat_1(k2_zfmisc_1(X0,X1),X2) ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_1539,c_1542]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_31775,plain,
% 11.73/2.00      ( k9_relat_1(k2_zfmisc_1(X0,X1),k1_relat_1(sK6)) = k11_relat_1(k2_zfmisc_1(X0,X1),sK3)
% 11.73/2.00      | k1_relat_1(sK6) = k1_xboole_0 ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_31754,c_6598]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_43,negated_conjecture,
% 11.73/2.00      ( v1_funct_1(sK6) ),
% 11.73/2.00      inference(cnf_transformation,[],[f114]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_44,plain,
% 11.73/2.00      ( v1_funct_1(sK6) = iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_40,negated_conjecture,
% 11.73/2.00      ( ~ r1_tarski(k7_relset_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4,sK6,sK5),k6_enumset1(k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3))) ),
% 11.73/2.00      inference(cnf_transformation,[],[f129]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_38,plain,
% 11.73/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.73/2.00      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 11.73/2.00      inference(cnf_transformation,[],[f112]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_1950,plain,
% 11.73/2.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)))
% 11.73/2.00      | k7_relset_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4,sK6,X0) = k9_relat_1(sK6,X0) ),
% 11.73/2.00      inference(instantiation,[status(thm)],[c_38]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_2123,plain,
% 11.73/2.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)))
% 11.73/2.00      | k7_relset_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4,sK6,sK5) = k9_relat_1(sK6,sK5) ),
% 11.73/2.00      inference(instantiation,[status(thm)],[c_1950]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_2274,plain,
% 11.73/2.00      ( v1_relat_1(sK6) = iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_2273]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_32,plain,
% 11.73/2.00      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 11.73/2.00      inference(cnf_transformation,[],[f106]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_12423,plain,
% 11.73/2.00      ( r1_tarski(k9_relat_1(sK6,X0),k2_relat_1(sK6)) | ~ v1_relat_1(sK6) ),
% 11.73/2.00      inference(instantiation,[status(thm)],[c_32]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_31558,plain,
% 11.73/2.00      ( r1_tarski(k9_relat_1(sK6,sK5),k2_relat_1(sK6)) | ~ v1_relat_1(sK6) ),
% 11.73/2.00      inference(instantiation,[status(thm)],[c_12423]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_687,plain,
% 11.73/2.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.73/2.00      theory(equality) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_1938,plain,
% 11.73/2.00      ( ~ r1_tarski(X0,X1)
% 11.73/2.00      | r1_tarski(k7_relset_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4,sK6,sK5),k6_enumset1(k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3)))
% 11.73/2.00      | k6_enumset1(k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3)) != X1
% 11.73/2.00      | k7_relset_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4,sK6,sK5) != X0 ),
% 11.73/2.00      inference(instantiation,[status(thm)],[c_687]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_2122,plain,
% 11.73/2.00      ( r1_tarski(k7_relset_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4,sK6,sK5),k6_enumset1(k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3)))
% 11.73/2.00      | ~ r1_tarski(k9_relat_1(sK6,sK5),X0)
% 11.73/2.00      | k6_enumset1(k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3)) != X0
% 11.73/2.00      | k7_relset_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4,sK6,sK5) != k9_relat_1(sK6,sK5) ),
% 11.73/2.00      inference(instantiation,[status(thm)],[c_1938]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_31563,plain,
% 11.73/2.00      ( r1_tarski(k7_relset_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4,sK6,sK5),k6_enumset1(k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3)))
% 11.73/2.00      | ~ r1_tarski(k9_relat_1(sK6,sK5),k2_relat_1(sK6))
% 11.73/2.00      | k6_enumset1(k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3)) != k2_relat_1(sK6)
% 11.73/2.00      | k7_relset_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4,sK6,sK5) != k9_relat_1(sK6,sK5) ),
% 11.73/2.00      inference(instantiation,[status(thm)],[c_2122]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_24,plain,
% 11.73/2.00      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
% 11.73/2.00      inference(cnf_transformation,[],[f145]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_1545,plain,
% 11.73/2.00      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) = iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_14,plain,
% 11.73/2.00      ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7) ),
% 11.73/2.00      inference(cnf_transformation,[],[f137]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_1555,plain,
% 11.73/2.00      ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7) = iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_12,plain,
% 11.73/2.00      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
% 11.73/2.00      | ~ sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9)
% 11.73/2.00      | r2_hidden(X0,X9) ),
% 11.73/2.00      inference(cnf_transformation,[],[f85]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_1557,plain,
% 11.73/2.00      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) != iProver_top
% 11.73/2.00      | sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9) != iProver_top
% 11.73/2.00      | r2_hidden(X0,X9) = iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_9568,plain,
% 11.73/2.00      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != iProver_top
% 11.73/2.00      | r2_hidden(X7,X8) = iProver_top ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_1555,c_1557]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_21401,plain,
% 11.73/2.00      ( r2_hidden(X0,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X0)) = iProver_top ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_1545,c_9568]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_31776,plain,
% 11.73/2.00      ( k1_relat_1(sK6) = k1_xboole_0
% 11.73/2.00      | r2_hidden(sK3,k1_relat_1(sK6)) = iProver_top ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_31754,c_21401]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_36,plain,
% 11.73/2.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 11.73/2.00      | ~ v1_funct_1(X1)
% 11.73/2.00      | ~ v1_relat_1(X1)
% 11.73/2.00      | k6_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ),
% 11.73/2.00      inference(cnf_transformation,[],[f128]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_1535,plain,
% 11.73/2.00      ( k6_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k11_relat_1(X0,X1)
% 11.73/2.00      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 11.73/2.00      | v1_funct_1(X0) != iProver_top
% 11.73/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_32692,plain,
% 11.73/2.00      ( k6_enumset1(k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3)) = k11_relat_1(sK6,sK3)
% 11.73/2.00      | k1_relat_1(sK6) = k1_xboole_0
% 11.73/2.00      | v1_funct_1(sK6) != iProver_top
% 11.73/2.00      | v1_relat_1(sK6) != iProver_top ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_31776,c_1535]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_1543,plain,
% 11.73/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.73/2.00      | r1_tarski(X0,X1) = iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_2976,plain,
% 11.73/2.00      ( r1_tarski(sK6,k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) = iProver_top ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_1530,c_1543]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_1528,plain,
% 11.73/2.00      ( r1_tarski(X0,X1) != iProver_top
% 11.73/2.00      | v1_relat_1(X1) != iProver_top
% 11.73/2.00      | v1_relat_1(X0) = iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_337]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_2980,plain,
% 11.73/2.00      ( v1_relat_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != iProver_top
% 11.73/2.00      | v1_relat_1(sK6) = iProver_top ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_2976,c_1528]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_3399,plain,
% 11.73/2.00      ( v1_relat_1(sK6) = iProver_top ),
% 11.73/2.00      inference(global_propositional_subsumption,[status(thm)],[c_2980,c_2274]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_6599,plain,
% 11.73/2.00      ( k9_relat_1(sK6,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k11_relat_1(sK6,X0) ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_3399,c_1542]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_35,plain,
% 11.73/2.00      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 11.73/2.00      inference(cnf_transformation,[],[f109]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_1536,plain,
% 11.73/2.00      ( k7_relat_1(X0,X1) = X0
% 11.73/2.00      | v4_relat_1(X0,X1) != iProver_top
% 11.73/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_4823,plain,
% 11.73/2.00      ( k7_relat_1(sK6,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = sK6
% 11.73/2.00      | v1_relat_1(sK6) != iProver_top ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_3854,c_1536]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_1895,plain,
% 11.73/2.00      ( v4_relat_1(sK6,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))
% 11.73/2.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4))) ),
% 11.73/2.00      inference(instantiation,[status(thm)],[c_37]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_2045,plain,
% 11.73/2.00      ( ~ v4_relat_1(sK6,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))
% 11.73/2.00      | ~ v1_relat_1(sK6)
% 11.73/2.00      | k7_relat_1(sK6,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = sK6 ),
% 11.73/2.00      inference(instantiation,[status(thm)],[c_35]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_5556,plain,
% 11.73/2.00      ( k7_relat_1(sK6,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = sK6 ),
% 11.73/2.00      inference(global_propositional_subsumption,
% 11.73/2.00                [status(thm)],
% 11.73/2.00                [c_4823,c_42,c_1895,c_2045,c_2273]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_33,plain,
% 11.73/2.00      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 11.73/2.00      inference(cnf_transformation,[],[f107]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_1537,plain,
% 11.73/2.00      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 11.73/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_3932,plain,
% 11.73/2.00      ( k2_relat_1(k7_relat_1(sK6,X0)) = k9_relat_1(sK6,X0) ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_3399,c_1537]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_5562,plain,
% 11.73/2.00      ( k9_relat_1(sK6,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = k2_relat_1(sK6) ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_5556,c_3932]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_6634,plain,
% 11.73/2.00      ( k11_relat_1(sK6,sK3) = k2_relat_1(sK6) ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_6599,c_5562]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_32693,plain,
% 11.73/2.00      ( k6_enumset1(k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3)) = k2_relat_1(sK6)
% 11.73/2.00      | k1_relat_1(sK6) = k1_xboole_0
% 11.73/2.00      | v1_funct_1(sK6) != iProver_top
% 11.73/2.00      | v1_relat_1(sK6) != iProver_top ),
% 11.73/2.00      inference(light_normalisation,[status(thm)],[c_32692,c_6634]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_32695,plain,
% 11.73/2.00      ( k1_relat_1(sK6) = k1_xboole_0 ),
% 11.73/2.00      inference(global_propositional_subsumption,
% 11.73/2.00                [status(thm)],
% 11.73/2.00                [c_31775,c_44,c_42,c_40,c_2123,c_2273,c_2274,c_31558,c_31563,
% 11.73/2.00                 c_32693]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_31774,plain,
% 11.73/2.00      ( k1_relat_1(sK6) = k1_xboole_0
% 11.73/2.00      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK4))) = iProver_top ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_31754,c_1530]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_45,plain,
% 11.73/2.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4))) = iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_39,plain,
% 11.73/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.73/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 11.73/2.00      | ~ r1_tarski(k1_relat_1(X0),X3) ),
% 11.73/2.00      inference(cnf_transformation,[],[f113]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_1923,plain,
% 11.73/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.73/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X2)))
% 11.73/2.00      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) ),
% 11.73/2.00      inference(instantiation,[status(thm)],[c_39]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_2995,plain,
% 11.73/2.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)))
% 11.73/2.00      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK4)))
% 11.73/2.00      | ~ r1_tarski(k1_relat_1(sK6),k1_relat_1(sK6)) ),
% 11.73/2.00      inference(instantiation,[status(thm)],[c_1923]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_2996,plain,
% 11.73/2.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4))) != iProver_top
% 11.73/2.00      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK4))) = iProver_top
% 11.73/2.00      | r1_tarski(k1_relat_1(sK6),k1_relat_1(sK6)) != iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_2995]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_1,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f131]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_1924,plain,
% 11.73/2.00      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) ),
% 11.73/2.00      inference(instantiation,[status(thm)],[c_1]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_3189,plain,
% 11.73/2.00      ( r1_tarski(k1_relat_1(sK6),k1_relat_1(sK6)) ),
% 11.73/2.00      inference(instantiation,[status(thm)],[c_1924]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_3190,plain,
% 11.73/2.00      ( r1_tarski(k1_relat_1(sK6),k1_relat_1(sK6)) = iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_3189]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_31872,plain,
% 11.73/2.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK4))) = iProver_top ),
% 11.73/2.00      inference(global_propositional_subsumption,
% 11.73/2.00                [status(thm)],
% 11.73/2.00                [c_31774,c_45,c_2996,c_3190]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_31877,plain,
% 11.73/2.00      ( r1_tarski(sK6,k2_zfmisc_1(k1_relat_1(sK6),sK4)) = iProver_top ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_31872,c_1543]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_32699,plain,
% 11.73/2.00      ( r1_tarski(sK6,k2_zfmisc_1(k1_xboole_0,sK4)) = iProver_top ),
% 11.73/2.00      inference(demodulation,[status(thm)],[c_32695,c_31877]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_8,plain,
% 11.73/2.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 11.73/2.00      inference(cnf_transformation,[],[f136]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_32785,plain,
% 11.73/2.00      ( r1_tarski(sK6,k1_xboole_0) = iProver_top ),
% 11.73/2.00      inference(demodulation,[status(thm)],[c_32699,c_8]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_3,plain,
% 11.73/2.00      ( r1_tarski(k1_xboole_0,X0) ),
% 11.73/2.00      inference(cnf_transformation,[],[f70]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_1563,plain,
% 11.73/2.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_0,plain,
% 11.73/2.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 11.73/2.00      inference(cnf_transformation,[],[f69]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_1565,plain,
% 11.73/2.00      ( X0 = X1
% 11.73/2.00      | r1_tarski(X0,X1) != iProver_top
% 11.73/2.00      | r1_tarski(X1,X0) != iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_4775,plain,
% 11.73/2.00      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_1563,c_1565]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_33849,plain,
% 11.73/2.00      ( sK6 = k1_xboole_0 ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_32785,c_4775]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_1533,plain,
% 11.73/2.00      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 11.73/2.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_5013,plain,
% 11.73/2.00      ( k7_relset_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4,sK6,X0) = k9_relat_1(sK6,X0) ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_1530,c_1533]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_1531,plain,
% 11.73/2.00      ( r1_tarski(k7_relset_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4,sK6,sK5),k6_enumset1(k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3))) != iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_5277,plain,
% 11.73/2.00      ( r1_tarski(k9_relat_1(sK6,sK5),k6_enumset1(k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3),k1_funct_1(sK6,sK3))) != iProver_top ),
% 11.73/2.00      inference(demodulation,[status(thm)],[c_5013,c_1531]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_35426,plain,
% 11.73/2.00      ( r1_tarski(k9_relat_1(k1_xboole_0,sK5),k6_enumset1(k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3))) != iProver_top ),
% 11.73/2.00      inference(demodulation,[status(thm)],[c_33849,c_5277]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_34,plain,
% 11.73/2.00      ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 11.73/2.00      inference(cnf_transformation,[],[f108]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_35458,plain,
% 11.73/2.00      ( r1_tarski(k1_xboole_0,k6_enumset1(k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3))) != iProver_top ),
% 11.73/2.00      inference(demodulation,[status(thm)],[c_35426,c_34]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_35600,plain,
% 11.73/2.00      ( $false ),
% 11.73/2.00      inference(forward_subsumption_resolution,[status(thm)],[c_35458,c_1563]) ).
% 11.73/2.00  
% 11.73/2.00  
% 11.73/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.73/2.00  
% 11.73/2.00  ------                               Statistics
% 11.73/2.00  
% 11.73/2.00  ------ Selected
% 11.73/2.00  
% 11.73/2.00  total_time:                             1.118
% 11.73/2.00  
%------------------------------------------------------------------------------
