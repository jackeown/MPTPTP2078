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
% DateTime   : Thu Dec  3 12:05:49 EST 2020

% Result     : Theorem 11.90s
% Output     : CNFRefutation 11.90s
% Verified   : 
% Statistics : Number of formulae       :  204 (1193 expanded)
%              Number of clauses        :   94 ( 246 expanded)
%              Number of leaves         :   30 ( 302 expanded)
%              Depth                    :   25
%              Number of atoms          :  608 (2443 expanded)
%              Number of equality atoms :  345 (1241 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   30 (   2 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f62,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
        & k1_xboole_0 != X1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k7_relset_1(k1_tarski(sK2),sK3,sK5,sK4),k1_tarski(k1_funct_1(sK5,sK2)))
      & k1_xboole_0 != sK3
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK2),sK3,sK5,sK4),k1_tarski(k1_funct_1(sK5,sK2)))
    & k1_xboole_0 != sK3
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f45,f62])).

fof(f113,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) ),
    inference(cnf_transformation,[],[f63])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f116,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f73,f74])).

fof(f117,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f72,f116])).

fof(f118,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f71,f117])).

fof(f119,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f70,f118])).

fof(f120,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f69,f119])).

fof(f121,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f68,f120])).

fof(f130,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) ),
    inference(definition_unfolding,[],[f113,f121])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f101,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f50])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f124,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f75,f121,f121])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f97,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f99,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f98,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f17,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f103,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ~ ( X5 != X7
              & X4 != X7
              & X3 != X7
              & X2 != X7
              & X1 != X7
              & X0 != X7 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ( X5 = X7
            | X4 = X7
            | X3 = X7
            | X2 = X7
            | X1 = X7
            | X0 = X7 ) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f46,plain,(
    ! [X5,X4,X3,X2,X1,X0,X6] :
      ( sP0(X5,X4,X3,X2,X1,X0,X6)
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ( X5 = X7
            | X4 = X7
            | X3 = X7
            | X2 = X7
            | X1 = X7
            | X0 = X7 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> sP0(X5,X4,X3,X2,X1,X0,X6) ) ),
    inference(definition_folding,[],[f30,f46])).

fof(f59,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
        | ~ sP0(X5,X4,X3,X2,X1,X0,X6) )
      & ( sP0(X5,X4,X3,X2,X1,X0,X6)
        | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f95,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( sP0(X5,X4,X3,X2,X1,X0,X6)
      | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f126,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( sP0(X5,X4,X3,X2,X1,X0,X6)
      | k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(definition_unfolding,[],[f95,f116])).

fof(f143,plain,(
    ! [X4,X2,X0,X5,X3,X1] : sP0(X5,X4,X3,X2,X1,X0,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) ),
    inference(equality_resolution,[],[f126])).

fof(f115,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK2),sK3,sK5,sK4),k1_tarski(k1_funct_1(sK5,sK2))) ),
    inference(cnf_transformation,[],[f63])).

fof(f129,plain,(
    ~ r1_tarski(k7_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK5,sK4),k6_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2))) ),
    inference(definition_unfolding,[],[f115,f121,f121])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f110,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f104,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f54,plain,(
    ! [X5,X4,X3,X2,X1,X0,X6] :
      ( ( sP0(X5,X4,X3,X2,X1,X0,X6)
        | ? [X7] :
            ( ( ( X5 != X7
                & X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 )
              | ~ r2_hidden(X7,X6) )
            & ( X5 = X7
              | X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | r2_hidden(X7,X6) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X6)
              | ( X5 != X7
                & X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 ) )
            & ( X5 = X7
              | X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | ~ r2_hidden(X7,X6) ) )
        | ~ sP0(X5,X4,X3,X2,X1,X0,X6) ) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f55,plain,(
    ! [X5,X4,X3,X2,X1,X0,X6] :
      ( ( sP0(X5,X4,X3,X2,X1,X0,X6)
        | ? [X7] :
            ( ( ( X5 != X7
                & X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 )
              | ~ r2_hidden(X7,X6) )
            & ( X5 = X7
              | X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | r2_hidden(X7,X6) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X6)
              | ( X5 != X7
                & X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 ) )
            & ( X5 = X7
              | X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | ~ r2_hidden(X7,X6) ) )
        | ~ sP0(X5,X4,X3,X2,X1,X0,X6) ) ) ),
    inference(flattening,[],[f54])).

fof(f56,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6)
        | ? [X7] :
            ( ( ( X0 != X7
                & X1 != X7
                & X2 != X7
                & X3 != X7
                & X4 != X7
                & X5 != X7 )
              | ~ r2_hidden(X7,X6) )
            & ( X0 = X7
              | X1 = X7
              | X2 = X7
              | X3 = X7
              | X4 = X7
              | X5 = X7
              | r2_hidden(X7,X6) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X6)
              | ( X0 != X8
                & X1 != X8
                & X2 != X8
                & X3 != X8
                & X4 != X8
                & X5 != X8 ) )
            & ( X0 = X8
              | X1 = X8
              | X2 = X8
              | X3 = X8
              | X4 = X8
              | X5 = X8
              | ~ r2_hidden(X8,X6) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6) ) ) ),
    inference(rectify,[],[f55])).

fof(f57,plain,(
    ! [X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X7] :
          ( ( ( X0 != X7
              & X1 != X7
              & X2 != X7
              & X3 != X7
              & X4 != X7
              & X5 != X7 )
            | ~ r2_hidden(X7,X6) )
          & ( X0 = X7
            | X1 = X7
            | X2 = X7
            | X3 = X7
            | X4 = X7
            | X5 = X7
            | r2_hidden(X7,X6) ) )
     => ( ( ( sK1(X0,X1,X2,X3,X4,X5,X6) != X0
            & sK1(X0,X1,X2,X3,X4,X5,X6) != X1
            & sK1(X0,X1,X2,X3,X4,X5,X6) != X2
            & sK1(X0,X1,X2,X3,X4,X5,X6) != X3
            & sK1(X0,X1,X2,X3,X4,X5,X6) != X4
            & sK1(X0,X1,X2,X3,X4,X5,X6) != X5 )
          | ~ r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6),X6) )
        & ( sK1(X0,X1,X2,X3,X4,X5,X6) = X0
          | sK1(X0,X1,X2,X3,X4,X5,X6) = X1
          | sK1(X0,X1,X2,X3,X4,X5,X6) = X2
          | sK1(X0,X1,X2,X3,X4,X5,X6) = X3
          | sK1(X0,X1,X2,X3,X4,X5,X6) = X4
          | sK1(X0,X1,X2,X3,X4,X5,X6) = X5
          | r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6),X6) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6)
        | ( ( ( sK1(X0,X1,X2,X3,X4,X5,X6) != X0
              & sK1(X0,X1,X2,X3,X4,X5,X6) != X1
              & sK1(X0,X1,X2,X3,X4,X5,X6) != X2
              & sK1(X0,X1,X2,X3,X4,X5,X6) != X3
              & sK1(X0,X1,X2,X3,X4,X5,X6) != X4
              & sK1(X0,X1,X2,X3,X4,X5,X6) != X5 )
            | ~ r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6),X6) )
          & ( sK1(X0,X1,X2,X3,X4,X5,X6) = X0
            | sK1(X0,X1,X2,X3,X4,X5,X6) = X1
            | sK1(X0,X1,X2,X3,X4,X5,X6) = X2
            | sK1(X0,X1,X2,X3,X4,X5,X6) = X3
            | sK1(X0,X1,X2,X3,X4,X5,X6) = X4
            | sK1(X0,X1,X2,X3,X4,X5,X6) = X5
            | r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6),X6) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X6)
              | ( X0 != X8
                & X1 != X8
                & X2 != X8
                & X3 != X8
                & X4 != X8
                & X5 != X8 ) )
            & ( X0 = X8
              | X1 = X8
              | X2 = X8
              | X3 = X8
              | X4 = X8
              | X5 = X8
              | ~ r2_hidden(X8,X6) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f56,f57])).

fof(f83,plain,(
    ! [X6,X4,X2,X0,X8,X5,X3,X1] :
      ( r2_hidden(X8,X6)
      | X4 != X8
      | ~ sP0(X0,X1,X2,X3,X4,X5,X6) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f141,plain,(
    ! [X6,X2,X0,X8,X5,X3,X1] :
      ( r2_hidden(X8,X6)
      | ~ sP0(X0,X1,X2,X3,X8,X5,X6) ) ),
    inference(equality_resolution,[],[f83])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f108,plain,(
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
    inference(definition_unfolding,[],[f108,f121])).

fof(f112,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f63])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f100,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f127,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f100,f121])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f107,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f105,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f25,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f111,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f48])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f131,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f65])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f52])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f136,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f79])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f66,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f20,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f106,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_43,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_6318,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_38,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_6322,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_7506,plain,
    ( v4_relat_1(sK5,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6318,c_6322])).

cnf(c_31,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_6327,plain,
    ( v4_relat_1(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f124])).

cnf(c_6348,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_11336,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_relat_1(X1)
    | k1_relat_1(X1) = k1_xboole_0
    | v4_relat_1(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6327,c_6348])).

cnf(c_39684,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_relat_1(sK5)
    | k1_relat_1(sK5) = k1_xboole_0
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_7506,c_11336])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_6330,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_6853,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6318,c_6330])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_26,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_312,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_26])).

cnf(c_313,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_312])).

cnf(c_388,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_28,c_313])).

cnf(c_6317,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_388])).

cnf(c_6997,plain,
    ( v1_relat_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_6853,c_6317])).

cnf(c_32,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_6326,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_7002,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6997,c_6326])).

cnf(c_42531,plain,
    ( k1_relat_1(sK5) = k1_xboole_0
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_relat_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_39684,c_7002])).

cnf(c_42532,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_relat_1(sK5)
    | k1_relat_1(sK5) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_42531])).

cnf(c_25,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,k6_enumset1(X5,X5,X5,X4,X3,X2,X1,X0)) ),
    inference(cnf_transformation,[],[f143])).

cnf(c_6332,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,k6_enumset1(X5,X5,X5,X4,X3,X2,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_42544,plain,
    ( k1_relat_1(sK5) = k1_xboole_0
    | sP0(sK2,sK2,sK2,sK2,sK2,sK2,k1_relat_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_42532,c_6332])).

cnf(c_41,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK5,sK4),k6_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2))) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_39,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_6736,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))
    | k7_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK5,X0) = k9_relat_1(sK5,X0) ),
    inference(instantiation,[status(thm)],[c_39])).

cnf(c_6828,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))
    | k7_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK5,sK4) = k9_relat_1(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_6736])).

cnf(c_7003,plain,
    ( v1_relat_1(sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7002])).

cnf(c_33,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_9528,plain,
    ( r1_tarski(k9_relat_1(sK5,X0),k2_relat_1(sK5))
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_13832,plain,
    ( r1_tarski(k9_relat_1(sK5,sK4),k2_relat_1(sK5))
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_9528])).

cnf(c_5444,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_6724,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k7_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK5,sK4),k6_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2)))
    | k6_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2)) != X1
    | k7_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK5,sK4) != X0 ),
    inference(instantiation,[status(thm)],[c_5444])).

cnf(c_6827,plain,
    ( r1_tarski(k7_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK5,sK4),k6_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2)))
    | ~ r1_tarski(k9_relat_1(sK5,sK4),X0)
    | k6_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2)) != X0
    | k7_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK5,sK4) != k9_relat_1(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_6724])).

cnf(c_13835,plain,
    ( r1_tarski(k7_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK5,sK4),k6_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2)))
    | ~ r1_tarski(k9_relat_1(sK5,sK4),k2_relat_1(sK5))
    | k6_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2)) != k2_relat_1(sK5)
    | k7_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK5,sK4) != k9_relat_1(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_6827])).

cnf(c_21,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6)
    | r2_hidden(X4,X6) ),
    inference(cnf_transformation,[],[f141])).

cnf(c_6336,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6) != iProver_top
    | r2_hidden(X4,X6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_10626,plain,
    ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X0,X2,X3,X4,X5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6332,c_6336])).

cnf(c_42552,plain,
    ( k1_relat_1(sK5) = k1_xboole_0
    | r2_hidden(sK2,k1_relat_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_42532,c_10626])).

cnf(c_37,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k6_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_44,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_522,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k6_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_37,c_44])).

cnf(c_523,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK5))
    | ~ v1_relat_1(sK5)
    | k6_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k11_relat_1(sK5,X0) ),
    inference(unflattening,[status(thm)],[c_522])).

cnf(c_6316,plain,
    ( k6_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k11_relat_1(sK5,X0)
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_523])).

cnf(c_45036,plain,
    ( k6_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2)) = k11_relat_1(sK5,sK2)
    | k1_relat_1(sK5) = k1_xboole_0
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_42552,c_6316])).

cnf(c_29,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_6329,plain,
    ( k9_relat_1(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k11_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_10326,plain,
    ( k9_relat_1(sK5,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k11_relat_1(sK5,X0) ),
    inference(superposition,[status(thm)],[c_7002,c_6329])).

cnf(c_36,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_6323,plain,
    ( k7_relat_1(X0,X1) = X0
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_10512,plain,
    ( k7_relat_1(sK5,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = sK5
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_7506,c_6323])).

cnf(c_10883,plain,
    ( k7_relat_1(sK5,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10512,c_7002])).

cnf(c_34,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_6324,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_7126,plain,
    ( k2_relat_1(k7_relat_1(sK5,X0)) = k9_relat_1(sK5,X0) ),
    inference(superposition,[status(thm)],[c_7002,c_6324])).

cnf(c_10890,plain,
    ( k9_relat_1(sK5,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_10883,c_7126])).

cnf(c_13725,plain,
    ( k11_relat_1(sK5,sK2) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_10326,c_10890])).

cnf(c_45040,plain,
    ( k6_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2)) = k2_relat_1(sK5)
    | k1_relat_1(sK5) = k1_xboole_0
    | v1_relat_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_45036,c_13725])).

cnf(c_45074,plain,
    ( k1_relat_1(sK5) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_42544,c_43,c_41,c_6828,c_7002,c_7003,c_13832,c_13835,c_45040])).

cnf(c_42551,plain,
    ( k1_relat_1(sK5) = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_42532,c_6318])).

cnf(c_46,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_40,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_6707,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X2)))
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_40])).

cnf(c_7475,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),sK3)))
    | ~ r1_tarski(k1_relat_1(sK5),k1_relat_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_6707])).

cnf(c_7476,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),sK3))) = iProver_top
    | r1_tarski(k1_relat_1(sK5),k1_relat_1(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7475])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_6708,plain,
    ( r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_7860,plain,
    ( r1_tarski(k1_relat_1(sK5),k1_relat_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_6708])).

cnf(c_7861,plain,
    ( r1_tarski(k1_relat_1(sK5),k1_relat_1(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7860])).

cnf(c_42642,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_42551,c_46,c_7476,c_7861])).

cnf(c_42647,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(k1_relat_1(sK5),sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_42642,c_6330])).

cnf(c_45078,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(k1_xboole_0,sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_45074,c_42647])).

cnf(c_8,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f136])).

cnf(c_46062,plain,
    ( r1_tarski(sK5,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_45078,c_8])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_6351,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_6353,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_9813,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6351,c_6353])).

cnf(c_49156,plain,
    ( sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_46062,c_9813])).

cnf(c_6321,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_10650,plain,
    ( k7_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK5,X0) = k9_relat_1(sK5,X0) ),
    inference(superposition,[status(thm)],[c_6318,c_6321])).

cnf(c_6319,plain,
    ( r1_tarski(k7_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK5,sK4),k6_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_10787,plain,
    ( r1_tarski(k9_relat_1(sK5,sK4),k6_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10650,c_6319])).

cnf(c_54567,plain,
    ( r1_tarski(k9_relat_1(k1_xboole_0,sK4),k6_enumset1(k1_funct_1(k1_xboole_0,sK2),k1_funct_1(k1_xboole_0,sK2),k1_funct_1(k1_xboole_0,sK2),k1_funct_1(k1_xboole_0,sK2),k1_funct_1(k1_xboole_0,sK2),k1_funct_1(k1_xboole_0,sK2),k1_funct_1(k1_xboole_0,sK2),k1_funct_1(k1_xboole_0,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_49156,c_10787])).

cnf(c_35,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_54611,plain,
    ( r1_tarski(k1_xboole_0,k6_enumset1(k1_funct_1(k1_xboole_0,sK2),k1_funct_1(k1_xboole_0,sK2),k1_funct_1(k1_xboole_0,sK2),k1_funct_1(k1_xboole_0,sK2),k1_funct_1(k1_xboole_0,sK2),k1_funct_1(k1_xboole_0,sK2),k1_funct_1(k1_xboole_0,sK2),k1_funct_1(k1_xboole_0,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_54567,c_35])).

cnf(c_54733,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_54611,c_6351])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:10:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.90/1.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.90/1.99  
% 11.90/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.90/1.99  
% 11.90/1.99  ------  iProver source info
% 11.90/1.99  
% 11.90/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.90/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.90/1.99  git: non_committed_changes: false
% 11.90/1.99  git: last_make_outside_of_git: false
% 11.90/1.99  
% 11.90/1.99  ------ 
% 11.90/1.99  
% 11.90/1.99  ------ Input Options
% 11.90/1.99  
% 11.90/1.99  --out_options                           all
% 11.90/1.99  --tptp_safe_out                         true
% 11.90/1.99  --problem_path                          ""
% 11.90/1.99  --include_path                          ""
% 11.90/1.99  --clausifier                            res/vclausify_rel
% 11.90/1.99  --clausifier_options                    --mode clausify
% 11.90/1.99  --stdin                                 false
% 11.90/1.99  --stats_out                             all
% 11.90/1.99  
% 11.90/1.99  ------ General Options
% 11.90/1.99  
% 11.90/1.99  --fof                                   false
% 11.90/1.99  --time_out_real                         305.
% 11.90/1.99  --time_out_virtual                      -1.
% 11.90/1.99  --symbol_type_check                     false
% 11.90/1.99  --clausify_out                          false
% 11.90/1.99  --sig_cnt_out                           false
% 11.90/1.99  --trig_cnt_out                          false
% 11.90/1.99  --trig_cnt_out_tolerance                1.
% 11.90/1.99  --trig_cnt_out_sk_spl                   false
% 11.90/1.99  --abstr_cl_out                          false
% 11.90/1.99  
% 11.90/1.99  ------ Global Options
% 11.90/1.99  
% 11.90/1.99  --schedule                              default
% 11.90/1.99  --add_important_lit                     false
% 11.90/1.99  --prop_solver_per_cl                    1000
% 11.90/1.99  --min_unsat_core                        false
% 11.90/1.99  --soft_assumptions                      false
% 11.90/1.99  --soft_lemma_size                       3
% 11.90/1.99  --prop_impl_unit_size                   0
% 11.90/1.99  --prop_impl_unit                        []
% 11.90/1.99  --share_sel_clauses                     true
% 11.90/1.99  --reset_solvers                         false
% 11.90/1.99  --bc_imp_inh                            [conj_cone]
% 11.90/1.99  --conj_cone_tolerance                   3.
% 11.90/1.99  --extra_neg_conj                        none
% 11.90/1.99  --large_theory_mode                     true
% 11.90/1.99  --prolific_symb_bound                   200
% 11.90/1.99  --lt_threshold                          2000
% 11.90/1.99  --clause_weak_htbl                      true
% 11.90/1.99  --gc_record_bc_elim                     false
% 11.90/1.99  
% 11.90/1.99  ------ Preprocessing Options
% 11.90/1.99  
% 11.90/1.99  --preprocessing_flag                    true
% 11.90/1.99  --time_out_prep_mult                    0.1
% 11.90/1.99  --splitting_mode                        input
% 11.90/1.99  --splitting_grd                         true
% 11.90/1.99  --splitting_cvd                         false
% 11.90/1.99  --splitting_cvd_svl                     false
% 11.90/1.99  --splitting_nvd                         32
% 11.90/1.99  --sub_typing                            true
% 11.90/1.99  --prep_gs_sim                           true
% 11.90/1.99  --prep_unflatten                        true
% 11.90/1.99  --prep_res_sim                          true
% 11.90/1.99  --prep_upred                            true
% 11.90/1.99  --prep_sem_filter                       exhaustive
% 11.90/1.99  --prep_sem_filter_out                   false
% 11.90/1.99  --pred_elim                             true
% 11.90/1.99  --res_sim_input                         true
% 11.90/1.99  --eq_ax_congr_red                       true
% 11.90/1.99  --pure_diseq_elim                       true
% 11.90/1.99  --brand_transform                       false
% 11.90/1.99  --non_eq_to_eq                          false
% 11.90/1.99  --prep_def_merge                        true
% 11.90/1.99  --prep_def_merge_prop_impl              false
% 11.90/1.99  --prep_def_merge_mbd                    true
% 11.90/1.99  --prep_def_merge_tr_red                 false
% 11.90/1.99  --prep_def_merge_tr_cl                  false
% 11.90/1.99  --smt_preprocessing                     true
% 11.90/1.99  --smt_ac_axioms                         fast
% 11.90/1.99  --preprocessed_out                      false
% 11.90/1.99  --preprocessed_stats                    false
% 11.90/1.99  
% 11.90/1.99  ------ Abstraction refinement Options
% 11.90/1.99  
% 11.90/1.99  --abstr_ref                             []
% 11.90/1.99  --abstr_ref_prep                        false
% 11.90/1.99  --abstr_ref_until_sat                   false
% 11.90/1.99  --abstr_ref_sig_restrict                funpre
% 11.90/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.90/1.99  --abstr_ref_under                       []
% 11.90/1.99  
% 11.90/1.99  ------ SAT Options
% 11.90/1.99  
% 11.90/1.99  --sat_mode                              false
% 11.90/1.99  --sat_fm_restart_options                ""
% 11.90/1.99  --sat_gr_def                            false
% 11.90/1.99  --sat_epr_types                         true
% 11.90/1.99  --sat_non_cyclic_types                  false
% 11.90/1.99  --sat_finite_models                     false
% 11.90/1.99  --sat_fm_lemmas                         false
% 11.90/1.99  --sat_fm_prep                           false
% 11.90/1.99  --sat_fm_uc_incr                        true
% 11.90/1.99  --sat_out_model                         small
% 11.90/1.99  --sat_out_clauses                       false
% 11.90/1.99  
% 11.90/1.99  ------ QBF Options
% 11.90/1.99  
% 11.90/1.99  --qbf_mode                              false
% 11.90/1.99  --qbf_elim_univ                         false
% 11.90/1.99  --qbf_dom_inst                          none
% 11.90/1.99  --qbf_dom_pre_inst                      false
% 11.90/1.99  --qbf_sk_in                             false
% 11.90/1.99  --qbf_pred_elim                         true
% 11.90/1.99  --qbf_split                             512
% 11.90/1.99  
% 11.90/1.99  ------ BMC1 Options
% 11.90/1.99  
% 11.90/1.99  --bmc1_incremental                      false
% 11.90/1.99  --bmc1_axioms                           reachable_all
% 11.90/1.99  --bmc1_min_bound                        0
% 11.90/1.99  --bmc1_max_bound                        -1
% 11.90/1.99  --bmc1_max_bound_default                -1
% 11.90/1.99  --bmc1_symbol_reachability              true
% 11.90/1.99  --bmc1_property_lemmas                  false
% 11.90/1.99  --bmc1_k_induction                      false
% 11.90/1.99  --bmc1_non_equiv_states                 false
% 11.90/1.99  --bmc1_deadlock                         false
% 11.90/1.99  --bmc1_ucm                              false
% 11.90/1.99  --bmc1_add_unsat_core                   none
% 11.90/1.99  --bmc1_unsat_core_children              false
% 11.90/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.90/1.99  --bmc1_out_stat                         full
% 11.90/1.99  --bmc1_ground_init                      false
% 11.90/1.99  --bmc1_pre_inst_next_state              false
% 11.90/1.99  --bmc1_pre_inst_state                   false
% 11.90/1.99  --bmc1_pre_inst_reach_state             false
% 11.90/1.99  --bmc1_out_unsat_core                   false
% 11.90/1.99  --bmc1_aig_witness_out                  false
% 11.90/1.99  --bmc1_verbose                          false
% 11.90/1.99  --bmc1_dump_clauses_tptp                false
% 11.90/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.90/1.99  --bmc1_dump_file                        -
% 11.90/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.90/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.90/1.99  --bmc1_ucm_extend_mode                  1
% 11.90/1.99  --bmc1_ucm_init_mode                    2
% 11.90/1.99  --bmc1_ucm_cone_mode                    none
% 11.90/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.90/1.99  --bmc1_ucm_relax_model                  4
% 11.90/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.90/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.90/1.99  --bmc1_ucm_layered_model                none
% 11.90/1.99  --bmc1_ucm_max_lemma_size               10
% 11.90/1.99  
% 11.90/1.99  ------ AIG Options
% 11.90/1.99  
% 11.90/1.99  --aig_mode                              false
% 11.90/1.99  
% 11.90/1.99  ------ Instantiation Options
% 11.90/1.99  
% 11.90/1.99  --instantiation_flag                    true
% 11.90/1.99  --inst_sos_flag                         false
% 11.90/1.99  --inst_sos_phase                        true
% 11.90/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.90/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.90/1.99  --inst_lit_sel_side                     num_symb
% 11.90/1.99  --inst_solver_per_active                1400
% 11.90/1.99  --inst_solver_calls_frac                1.
% 11.90/1.99  --inst_passive_queue_type               priority_queues
% 11.90/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.90/1.99  --inst_passive_queues_freq              [25;2]
% 11.90/1.99  --inst_dismatching                      true
% 11.90/1.99  --inst_eager_unprocessed_to_passive     true
% 11.90/1.99  --inst_prop_sim_given                   true
% 11.90/1.99  --inst_prop_sim_new                     false
% 11.90/1.99  --inst_subs_new                         false
% 11.90/1.99  --inst_eq_res_simp                      false
% 11.90/1.99  --inst_subs_given                       false
% 11.90/1.99  --inst_orphan_elimination               true
% 11.90/1.99  --inst_learning_loop_flag               true
% 11.90/1.99  --inst_learning_start                   3000
% 11.90/1.99  --inst_learning_factor                  2
% 11.90/1.99  --inst_start_prop_sim_after_learn       3
% 11.90/1.99  --inst_sel_renew                        solver
% 11.90/1.99  --inst_lit_activity_flag                true
% 11.90/1.99  --inst_restr_to_given                   false
% 11.90/1.99  --inst_activity_threshold               500
% 11.90/1.99  --inst_out_proof                        true
% 11.90/1.99  
% 11.90/1.99  ------ Resolution Options
% 11.90/1.99  
% 11.90/1.99  --resolution_flag                       true
% 11.90/1.99  --res_lit_sel                           adaptive
% 11.90/1.99  --res_lit_sel_side                      none
% 11.90/1.99  --res_ordering                          kbo
% 11.90/1.99  --res_to_prop_solver                    active
% 11.90/1.99  --res_prop_simpl_new                    false
% 11.90/1.99  --res_prop_simpl_given                  true
% 11.90/1.99  --res_passive_queue_type                priority_queues
% 11.90/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.90/1.99  --res_passive_queues_freq               [15;5]
% 11.90/1.99  --res_forward_subs                      full
% 11.90/1.99  --res_backward_subs                     full
% 11.90/1.99  --res_forward_subs_resolution           true
% 11.90/1.99  --res_backward_subs_resolution          true
% 11.90/1.99  --res_orphan_elimination                true
% 11.90/1.99  --res_time_limit                        2.
% 11.90/1.99  --res_out_proof                         true
% 11.90/1.99  
% 11.90/1.99  ------ Superposition Options
% 11.90/1.99  
% 11.90/1.99  --superposition_flag                    true
% 11.90/1.99  --sup_passive_queue_type                priority_queues
% 11.90/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.90/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.90/1.99  --demod_completeness_check              fast
% 11.90/1.99  --demod_use_ground                      true
% 11.90/1.99  --sup_to_prop_solver                    passive
% 11.90/1.99  --sup_prop_simpl_new                    true
% 11.90/1.99  --sup_prop_simpl_given                  true
% 11.90/1.99  --sup_fun_splitting                     false
% 11.90/1.99  --sup_smt_interval                      50000
% 11.90/1.99  
% 11.90/1.99  ------ Superposition Simplification Setup
% 11.90/1.99  
% 11.90/1.99  --sup_indices_passive                   []
% 11.90/1.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.90/1.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.90/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.90/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.90/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.90/1.99  --sup_full_bw                           [BwDemod]
% 11.90/1.99  --sup_immed_triv                        [TrivRules]
% 11.90/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.90/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.90/1.99  --sup_immed_bw_main                     []
% 11.90/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.90/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.90/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.90/1.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.90/1.99  
% 11.90/1.99  ------ Combination Options
% 11.90/1.99  
% 11.90/1.99  --comb_res_mult                         3
% 11.90/1.99  --comb_sup_mult                         2
% 11.90/1.99  --comb_inst_mult                        10
% 11.90/1.99  
% 11.90/1.99  ------ Debug Options
% 11.90/1.99  
% 11.90/1.99  --dbg_backtrace                         false
% 11.90/1.99  --dbg_dump_prop_clauses                 false
% 11.90/1.99  --dbg_dump_prop_clauses_file            -
% 11.90/1.99  --dbg_out_stat                          false
% 11.90/1.99  ------ Parsing...
% 11.90/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.90/1.99  
% 11.90/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.90/1.99  
% 11.90/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.90/1.99  
% 11.90/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.90/1.99  ------ Proving...
% 11.90/1.99  ------ Problem Properties 
% 11.90/1.99  
% 11.90/1.99  
% 11.90/1.99  clauses                                 43
% 11.90/1.99  conjectures                             3
% 11.90/1.99  EPR                                     12
% 11.90/1.99  Horn                                    39
% 11.90/1.99  unary                                   12
% 11.90/1.99  binary                                  14
% 11.90/1.99  lits                                    101
% 11.90/1.99  lits eq                                 34
% 11.90/1.99  fd_pure                                 0
% 11.90/1.99  fd_pseudo                               0
% 11.90/1.99  fd_cond                                 1
% 11.90/1.99  fd_pseudo_cond                          4
% 11.90/1.99  AC symbols                              0
% 11.90/1.99  
% 11.90/1.99  ------ Schedule dynamic 5 is on 
% 11.90/1.99  
% 11.90/1.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.90/1.99  
% 11.90/1.99  
% 11.90/1.99  ------ 
% 11.90/1.99  Current options:
% 11.90/1.99  ------ 
% 11.90/1.99  
% 11.90/1.99  ------ Input Options
% 11.90/1.99  
% 11.90/1.99  --out_options                           all
% 11.90/1.99  --tptp_safe_out                         true
% 11.90/1.99  --problem_path                          ""
% 11.90/1.99  --include_path                          ""
% 11.90/1.99  --clausifier                            res/vclausify_rel
% 11.90/1.99  --clausifier_options                    --mode clausify
% 11.90/1.99  --stdin                                 false
% 11.90/1.99  --stats_out                             all
% 11.90/1.99  
% 11.90/1.99  ------ General Options
% 11.90/1.99  
% 11.90/1.99  --fof                                   false
% 11.90/1.99  --time_out_real                         305.
% 11.90/1.99  --time_out_virtual                      -1.
% 11.90/1.99  --symbol_type_check                     false
% 11.90/1.99  --clausify_out                          false
% 11.90/1.99  --sig_cnt_out                           false
% 11.90/1.99  --trig_cnt_out                          false
% 11.90/1.99  --trig_cnt_out_tolerance                1.
% 11.90/1.99  --trig_cnt_out_sk_spl                   false
% 11.90/1.99  --abstr_cl_out                          false
% 11.90/1.99  
% 11.90/1.99  ------ Global Options
% 11.90/1.99  
% 11.90/1.99  --schedule                              default
% 11.90/1.99  --add_important_lit                     false
% 11.90/1.99  --prop_solver_per_cl                    1000
% 11.90/1.99  --min_unsat_core                        false
% 11.90/1.99  --soft_assumptions                      false
% 11.90/1.99  --soft_lemma_size                       3
% 11.90/1.99  --prop_impl_unit_size                   0
% 11.90/1.99  --prop_impl_unit                        []
% 11.90/1.99  --share_sel_clauses                     true
% 11.90/1.99  --reset_solvers                         false
% 11.90/1.99  --bc_imp_inh                            [conj_cone]
% 11.90/1.99  --conj_cone_tolerance                   3.
% 11.90/1.99  --extra_neg_conj                        none
% 11.90/1.99  --large_theory_mode                     true
% 11.90/1.99  --prolific_symb_bound                   200
% 11.90/1.99  --lt_threshold                          2000
% 11.90/1.99  --clause_weak_htbl                      true
% 11.90/1.99  --gc_record_bc_elim                     false
% 11.90/1.99  
% 11.90/1.99  ------ Preprocessing Options
% 11.90/1.99  
% 11.90/1.99  --preprocessing_flag                    true
% 11.90/1.99  --time_out_prep_mult                    0.1
% 11.90/1.99  --splitting_mode                        input
% 11.90/1.99  --splitting_grd                         true
% 11.90/1.99  --splitting_cvd                         false
% 11.90/1.99  --splitting_cvd_svl                     false
% 11.90/1.99  --splitting_nvd                         32
% 11.90/1.99  --sub_typing                            true
% 11.90/1.99  --prep_gs_sim                           true
% 11.90/1.99  --prep_unflatten                        true
% 11.90/1.99  --prep_res_sim                          true
% 11.90/1.99  --prep_upred                            true
% 11.90/1.99  --prep_sem_filter                       exhaustive
% 11.90/1.99  --prep_sem_filter_out                   false
% 11.90/1.99  --pred_elim                             true
% 11.90/1.99  --res_sim_input                         true
% 11.90/1.99  --eq_ax_congr_red                       true
% 11.90/1.99  --pure_diseq_elim                       true
% 11.90/1.99  --brand_transform                       false
% 11.90/1.99  --non_eq_to_eq                          false
% 11.90/1.99  --prep_def_merge                        true
% 11.90/1.99  --prep_def_merge_prop_impl              false
% 11.90/1.99  --prep_def_merge_mbd                    true
% 11.90/1.99  --prep_def_merge_tr_red                 false
% 11.90/1.99  --prep_def_merge_tr_cl                  false
% 11.90/1.99  --smt_preprocessing                     true
% 11.90/1.99  --smt_ac_axioms                         fast
% 11.90/1.99  --preprocessed_out                      false
% 11.90/1.99  --preprocessed_stats                    false
% 11.90/1.99  
% 11.90/1.99  ------ Abstraction refinement Options
% 11.90/1.99  
% 11.90/1.99  --abstr_ref                             []
% 11.90/1.99  --abstr_ref_prep                        false
% 11.90/1.99  --abstr_ref_until_sat                   false
% 11.90/1.99  --abstr_ref_sig_restrict                funpre
% 11.90/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.90/1.99  --abstr_ref_under                       []
% 11.90/1.99  
% 11.90/1.99  ------ SAT Options
% 11.90/1.99  
% 11.90/1.99  --sat_mode                              false
% 11.90/1.99  --sat_fm_restart_options                ""
% 11.90/1.99  --sat_gr_def                            false
% 11.90/1.99  --sat_epr_types                         true
% 11.90/1.99  --sat_non_cyclic_types                  false
% 11.90/1.99  --sat_finite_models                     false
% 11.90/1.99  --sat_fm_lemmas                         false
% 11.90/1.99  --sat_fm_prep                           false
% 11.90/1.99  --sat_fm_uc_incr                        true
% 11.90/1.99  --sat_out_model                         small
% 11.90/1.99  --sat_out_clauses                       false
% 11.90/1.99  
% 11.90/1.99  ------ QBF Options
% 11.90/1.99  
% 11.90/1.99  --qbf_mode                              false
% 11.90/1.99  --qbf_elim_univ                         false
% 11.90/1.99  --qbf_dom_inst                          none
% 11.90/1.99  --qbf_dom_pre_inst                      false
% 11.90/1.99  --qbf_sk_in                             false
% 11.90/1.99  --qbf_pred_elim                         true
% 11.90/1.99  --qbf_split                             512
% 11.90/1.99  
% 11.90/1.99  ------ BMC1 Options
% 11.90/1.99  
% 11.90/1.99  --bmc1_incremental                      false
% 11.90/1.99  --bmc1_axioms                           reachable_all
% 11.90/1.99  --bmc1_min_bound                        0
% 11.90/1.99  --bmc1_max_bound                        -1
% 11.90/1.99  --bmc1_max_bound_default                -1
% 11.90/1.99  --bmc1_symbol_reachability              true
% 11.90/1.99  --bmc1_property_lemmas                  false
% 11.90/1.99  --bmc1_k_induction                      false
% 11.90/1.99  --bmc1_non_equiv_states                 false
% 11.90/1.99  --bmc1_deadlock                         false
% 11.90/1.99  --bmc1_ucm                              false
% 11.90/1.99  --bmc1_add_unsat_core                   none
% 11.90/1.99  --bmc1_unsat_core_children              false
% 11.90/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.90/1.99  --bmc1_out_stat                         full
% 11.90/1.99  --bmc1_ground_init                      false
% 11.90/1.99  --bmc1_pre_inst_next_state              false
% 11.90/1.99  --bmc1_pre_inst_state                   false
% 11.90/1.99  --bmc1_pre_inst_reach_state             false
% 11.90/1.99  --bmc1_out_unsat_core                   false
% 11.90/1.99  --bmc1_aig_witness_out                  false
% 11.90/1.99  --bmc1_verbose                          false
% 11.90/1.99  --bmc1_dump_clauses_tptp                false
% 11.90/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.90/1.99  --bmc1_dump_file                        -
% 11.90/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.90/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.90/1.99  --bmc1_ucm_extend_mode                  1
% 11.90/1.99  --bmc1_ucm_init_mode                    2
% 11.90/1.99  --bmc1_ucm_cone_mode                    none
% 11.90/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.90/1.99  --bmc1_ucm_relax_model                  4
% 11.90/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.90/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.90/1.99  --bmc1_ucm_layered_model                none
% 11.90/1.99  --bmc1_ucm_max_lemma_size               10
% 11.90/1.99  
% 11.90/1.99  ------ AIG Options
% 11.90/1.99  
% 11.90/1.99  --aig_mode                              false
% 11.90/1.99  
% 11.90/1.99  ------ Instantiation Options
% 11.90/1.99  
% 11.90/1.99  --instantiation_flag                    true
% 11.90/1.99  --inst_sos_flag                         false
% 11.90/1.99  --inst_sos_phase                        true
% 11.90/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.90/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.90/1.99  --inst_lit_sel_side                     none
% 11.90/1.99  --inst_solver_per_active                1400
% 11.90/1.99  --inst_solver_calls_frac                1.
% 11.90/1.99  --inst_passive_queue_type               priority_queues
% 11.90/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.90/1.99  --inst_passive_queues_freq              [25;2]
% 11.90/1.99  --inst_dismatching                      true
% 11.90/1.99  --inst_eager_unprocessed_to_passive     true
% 11.90/1.99  --inst_prop_sim_given                   true
% 11.90/1.99  --inst_prop_sim_new                     false
% 11.90/1.99  --inst_subs_new                         false
% 11.90/1.99  --inst_eq_res_simp                      false
% 11.90/1.99  --inst_subs_given                       false
% 11.90/1.99  --inst_orphan_elimination               true
% 11.90/1.99  --inst_learning_loop_flag               true
% 11.90/1.99  --inst_learning_start                   3000
% 11.90/1.99  --inst_learning_factor                  2
% 11.90/1.99  --inst_start_prop_sim_after_learn       3
% 11.90/1.99  --inst_sel_renew                        solver
% 11.90/1.99  --inst_lit_activity_flag                true
% 11.90/1.99  --inst_restr_to_given                   false
% 11.90/1.99  --inst_activity_threshold               500
% 11.90/1.99  --inst_out_proof                        true
% 11.90/1.99  
% 11.90/1.99  ------ Resolution Options
% 11.90/1.99  
% 11.90/1.99  --resolution_flag                       false
% 11.90/1.99  --res_lit_sel                           adaptive
% 11.90/1.99  --res_lit_sel_side                      none
% 11.90/1.99  --res_ordering                          kbo
% 11.90/1.99  --res_to_prop_solver                    active
% 11.90/1.99  --res_prop_simpl_new                    false
% 11.90/1.99  --res_prop_simpl_given                  true
% 11.90/1.99  --res_passive_queue_type                priority_queues
% 11.90/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.90/1.99  --res_passive_queues_freq               [15;5]
% 11.90/1.99  --res_forward_subs                      full
% 11.90/1.99  --res_backward_subs                     full
% 11.90/1.99  --res_forward_subs_resolution           true
% 11.90/1.99  --res_backward_subs_resolution          true
% 11.90/1.99  --res_orphan_elimination                true
% 11.90/1.99  --res_time_limit                        2.
% 11.90/1.99  --res_out_proof                         true
% 11.90/1.99  
% 11.90/1.99  ------ Superposition Options
% 11.90/1.99  
% 11.90/1.99  --superposition_flag                    true
% 11.90/1.99  --sup_passive_queue_type                priority_queues
% 11.90/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.90/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.90/1.99  --demod_completeness_check              fast
% 11.90/1.99  --demod_use_ground                      true
% 11.90/1.99  --sup_to_prop_solver                    passive
% 11.90/1.99  --sup_prop_simpl_new                    true
% 11.90/1.99  --sup_prop_simpl_given                  true
% 11.90/1.99  --sup_fun_splitting                     false
% 11.90/1.99  --sup_smt_interval                      50000
% 11.90/1.99  
% 11.90/1.99  ------ Superposition Simplification Setup
% 11.90/1.99  
% 11.90/1.99  --sup_indices_passive                   []
% 11.90/1.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.90/1.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.90/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.90/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.90/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.90/1.99  --sup_full_bw                           [BwDemod]
% 11.90/1.99  --sup_immed_triv                        [TrivRules]
% 11.90/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.90/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.90/1.99  --sup_immed_bw_main                     []
% 11.90/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.90/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.90/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.90/1.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.90/1.99  
% 11.90/1.99  ------ Combination Options
% 11.90/1.99  
% 11.90/1.99  --comb_res_mult                         3
% 11.90/1.99  --comb_sup_mult                         2
% 11.90/1.99  --comb_inst_mult                        10
% 11.90/1.99  
% 11.90/1.99  ------ Debug Options
% 11.90/1.99  
% 11.90/1.99  --dbg_backtrace                         false
% 11.90/1.99  --dbg_dump_prop_clauses                 false
% 11.90/1.99  --dbg_dump_prop_clauses_file            -
% 11.90/1.99  --dbg_out_stat                          false
% 11.90/1.99  
% 11.90/1.99  
% 11.90/1.99  
% 11.90/1.99  
% 11.90/1.99  ------ Proving...
% 11.90/1.99  
% 11.90/1.99  
% 11.90/1.99  % SZS status Theorem for theBenchmark.p
% 11.90/1.99  
% 11.90/1.99   Resolution empty clause
% 11.90/1.99  
% 11.90/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.90/1.99  
% 11.90/1.99  fof(f26,conjecture,(
% 11.90/1.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 11.90/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.90/1.99  
% 11.90/1.99  fof(f27,negated_conjecture,(
% 11.90/1.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 11.90/1.99    inference(negated_conjecture,[],[f26])).
% 11.90/1.99  
% 11.90/1.99  fof(f28,plain,(
% 11.90/1.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 11.90/1.99    inference(pure_predicate_removal,[],[f27])).
% 11.90/1.99  
% 11.90/1.99  fof(f44,plain,(
% 11.90/1.99    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 11.90/1.99    inference(ennf_transformation,[],[f28])).
% 11.90/1.99  
% 11.90/1.99  fof(f45,plain,(
% 11.90/1.99    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 11.90/1.99    inference(flattening,[],[f44])).
% 11.90/1.99  
% 11.90/1.99  fof(f62,plain,(
% 11.90/1.99    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK2),sK3,sK5,sK4),k1_tarski(k1_funct_1(sK5,sK2))) & k1_xboole_0 != sK3 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) & v1_funct_1(sK5))),
% 11.90/1.99    introduced(choice_axiom,[])).
% 11.90/1.99  
% 11.90/1.99  fof(f63,plain,(
% 11.90/1.99    ~r1_tarski(k7_relset_1(k1_tarski(sK2),sK3,sK5,sK4),k1_tarski(k1_funct_1(sK5,sK2))) & k1_xboole_0 != sK3 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) & v1_funct_1(sK5)),
% 11.90/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f45,f62])).
% 11.90/1.99  
% 11.90/1.99  fof(f113,plain,(
% 11.90/1.99    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))),
% 11.90/1.99    inference(cnf_transformation,[],[f63])).
% 11.90/1.99  
% 11.90/1.99  fof(f3,axiom,(
% 11.90/1.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 11.90/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.90/1.99  
% 11.90/1.99  fof(f68,plain,(
% 11.90/1.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 11.90/1.99    inference(cnf_transformation,[],[f3])).
% 11.90/1.99  
% 11.90/1.99  fof(f4,axiom,(
% 11.90/1.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 11.90/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.90/1.99  
% 11.90/1.99  fof(f69,plain,(
% 11.90/1.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 11.90/1.99    inference(cnf_transformation,[],[f4])).
% 11.90/1.99  
% 11.90/1.99  fof(f5,axiom,(
% 11.90/1.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 11.90/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.90/1.99  
% 11.90/1.99  fof(f70,plain,(
% 11.90/1.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 11.90/1.99    inference(cnf_transformation,[],[f5])).
% 11.90/1.99  
% 11.90/1.99  fof(f6,axiom,(
% 11.90/1.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 11.90/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.90/1.99  
% 11.90/1.99  fof(f71,plain,(
% 11.90/1.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 11.90/1.99    inference(cnf_transformation,[],[f6])).
% 11.90/1.99  
% 11.90/1.99  fof(f7,axiom,(
% 11.90/1.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 11.90/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.90/1.99  
% 11.90/1.99  fof(f72,plain,(
% 11.90/1.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 11.90/1.99    inference(cnf_transformation,[],[f7])).
% 11.90/1.99  
% 11.90/1.99  fof(f8,axiom,(
% 11.90/1.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 11.90/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.90/1.99  
% 11.90/1.99  fof(f73,plain,(
% 11.90/1.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 11.90/1.99    inference(cnf_transformation,[],[f8])).
% 11.90/1.99  
% 11.90/1.99  fof(f9,axiom,(
% 11.90/1.99    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 11.90/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.90/1.99  
% 11.90/1.99  fof(f74,plain,(
% 11.90/1.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 11.90/1.99    inference(cnf_transformation,[],[f9])).
% 11.90/1.99  
% 11.90/1.99  fof(f116,plain,(
% 11.90/1.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 11.90/1.99    inference(definition_unfolding,[],[f73,f74])).
% 11.90/1.99  
% 11.90/1.99  fof(f117,plain,(
% 11.90/1.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 11.90/1.99    inference(definition_unfolding,[],[f72,f116])).
% 11.90/1.99  
% 11.90/1.99  fof(f118,plain,(
% 11.90/1.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 11.90/1.99    inference(definition_unfolding,[],[f71,f117])).
% 11.90/1.99  
% 11.90/1.99  fof(f119,plain,(
% 11.90/1.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 11.90/1.99    inference(definition_unfolding,[],[f70,f118])).
% 11.90/1.99  
% 11.90/1.99  fof(f120,plain,(
% 11.90/1.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 11.90/1.99    inference(definition_unfolding,[],[f69,f119])).
% 11.90/1.99  
% 11.90/1.99  fof(f121,plain,(
% 11.90/1.99    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 11.90/1.99    inference(definition_unfolding,[],[f68,f120])).
% 11.90/1.99  
% 11.90/1.99  fof(f130,plain,(
% 11.90/1.99    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))),
% 11.90/1.99    inference(definition_unfolding,[],[f113,f121])).
% 11.90/1.99  
% 11.90/1.99  fof(f23,axiom,(
% 11.90/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 11.90/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.90/1.99  
% 11.90/1.99  fof(f29,plain,(
% 11.90/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 11.90/1.99    inference(pure_predicate_removal,[],[f23])).
% 11.90/1.99  
% 11.90/1.99  fof(f40,plain,(
% 11.90/1.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.90/1.99    inference(ennf_transformation,[],[f29])).
% 11.90/1.99  
% 11.90/1.99  fof(f109,plain,(
% 11.90/1.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.90/1.99    inference(cnf_transformation,[],[f40])).
% 11.90/1.99  
% 11.90/1.99  fof(f16,axiom,(
% 11.90/1.99    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 11.90/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.90/1.99  
% 11.90/1.99  fof(f33,plain,(
% 11.90/1.99    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.90/1.99    inference(ennf_transformation,[],[f16])).
% 11.90/1.99  
% 11.90/1.99  fof(f61,plain,(
% 11.90/1.99    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 11.90/1.99    inference(nnf_transformation,[],[f33])).
% 11.90/1.99  
% 11.90/1.99  fof(f101,plain,(
% 11.90/1.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.90/1.99    inference(cnf_transformation,[],[f61])).
% 11.90/1.99  
% 11.90/1.99  fof(f10,axiom,(
% 11.90/1.99    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 11.90/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.90/1.99  
% 11.90/1.99  fof(f50,plain,(
% 11.90/1.99    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 11.90/1.99    inference(nnf_transformation,[],[f10])).
% 11.90/1.99  
% 11.90/1.99  fof(f51,plain,(
% 11.90/1.99    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 11.90/1.99    inference(flattening,[],[f50])).
% 11.90/1.99  
% 11.90/1.99  fof(f75,plain,(
% 11.90/1.99    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 11.90/1.99    inference(cnf_transformation,[],[f51])).
% 11.90/1.99  
% 11.90/1.99  fof(f124,plain,(
% 11.90/1.99    ( ! [X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 11.90/1.99    inference(definition_unfolding,[],[f75,f121,f121])).
% 11.90/1.99  
% 11.90/1.99  fof(f13,axiom,(
% 11.90/1.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 11.90/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.90/1.99  
% 11.90/1.99  fof(f60,plain,(
% 11.90/1.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 11.90/1.99    inference(nnf_transformation,[],[f13])).
% 11.90/1.99  
% 11.90/1.99  fof(f97,plain,(
% 11.90/1.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 11.90/1.99    inference(cnf_transformation,[],[f60])).
% 11.90/1.99  
% 11.90/1.99  fof(f14,axiom,(
% 11.90/1.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 11.90/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.90/1.99  
% 11.90/1.99  fof(f31,plain,(
% 11.90/1.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 11.90/1.99    inference(ennf_transformation,[],[f14])).
% 11.90/1.99  
% 11.90/1.99  fof(f99,plain,(
% 11.90/1.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 11.90/1.99    inference(cnf_transformation,[],[f31])).
% 11.90/1.99  
% 11.90/1.99  fof(f98,plain,(
% 11.90/1.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 11.90/1.99    inference(cnf_transformation,[],[f60])).
% 11.90/1.99  
% 11.90/1.99  fof(f17,axiom,(
% 11.90/1.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 11.90/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.90/1.99  
% 11.90/1.99  fof(f103,plain,(
% 11.90/1.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 11.90/1.99    inference(cnf_transformation,[],[f17])).
% 11.90/1.99  
% 11.90/1.99  fof(f12,axiom,(
% 11.90/1.99    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> ! [X7] : (r2_hidden(X7,X6) <=> ~(X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)))),
% 11.90/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.90/1.99  
% 11.90/1.99  fof(f30,plain,(
% 11.90/1.99    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> ! [X7] : (r2_hidden(X7,X6) <=> (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7)))),
% 11.90/1.99    inference(ennf_transformation,[],[f12])).
% 11.90/1.99  
% 11.90/1.99  fof(f46,plain,(
% 11.90/1.99    ! [X5,X4,X3,X2,X1,X0,X6] : (sP0(X5,X4,X3,X2,X1,X0,X6) <=> ! [X7] : (r2_hidden(X7,X6) <=> (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7)))),
% 11.90/1.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 11.90/1.99  
% 11.90/1.99  fof(f47,plain,(
% 11.90/1.99    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> sP0(X5,X4,X3,X2,X1,X0,X6))),
% 11.90/1.99    inference(definition_folding,[],[f30,f46])).
% 11.90/1.99  
% 11.90/1.99  fof(f59,plain,(
% 11.90/1.99    ! [X0,X1,X2,X3,X4,X5,X6] : ((k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 | ~sP0(X5,X4,X3,X2,X1,X0,X6)) & (sP0(X5,X4,X3,X2,X1,X0,X6) | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6))),
% 11.90/1.99    inference(nnf_transformation,[],[f47])).
% 11.90/1.99  
% 11.90/1.99  fof(f95,plain,(
% 11.90/1.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (sP0(X5,X4,X3,X2,X1,X0,X6) | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6) )),
% 11.90/1.99    inference(cnf_transformation,[],[f59])).
% 11.90/1.99  
% 11.90/1.99  fof(f126,plain,(
% 11.90/1.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (sP0(X5,X4,X3,X2,X1,X0,X6) | k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) != X6) )),
% 11.90/1.99    inference(definition_unfolding,[],[f95,f116])).
% 11.90/1.99  
% 11.90/1.99  fof(f143,plain,(
% 11.90/1.99    ( ! [X4,X2,X0,X5,X3,X1] : (sP0(X5,X4,X3,X2,X1,X0,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5))) )),
% 11.90/1.99    inference(equality_resolution,[],[f126])).
% 11.90/1.99  
% 11.90/1.99  fof(f115,plain,(
% 11.90/1.99    ~r1_tarski(k7_relset_1(k1_tarski(sK2),sK3,sK5,sK4),k1_tarski(k1_funct_1(sK5,sK2)))),
% 11.90/1.99    inference(cnf_transformation,[],[f63])).
% 11.90/1.99  
% 11.90/1.99  fof(f129,plain,(
% 11.90/1.99    ~r1_tarski(k7_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK5,sK4),k6_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2)))),
% 11.90/1.99    inference(definition_unfolding,[],[f115,f121,f121])).
% 11.90/1.99  
% 11.90/1.99  fof(f24,axiom,(
% 11.90/1.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 11.90/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.90/1.99  
% 11.90/1.99  fof(f41,plain,(
% 11.90/1.99    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.90/1.99    inference(ennf_transformation,[],[f24])).
% 11.90/1.99  
% 11.90/1.99  fof(f110,plain,(
% 11.90/1.99    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.90/1.99    inference(cnf_transformation,[],[f41])).
% 11.90/1.99  
% 11.90/1.99  fof(f18,axiom,(
% 11.90/1.99    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 11.90/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.90/1.99  
% 11.90/1.99  fof(f34,plain,(
% 11.90/1.99    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 11.90/1.99    inference(ennf_transformation,[],[f18])).
% 11.90/1.99  
% 11.90/1.99  fof(f104,plain,(
% 11.90/1.99    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 11.90/1.99    inference(cnf_transformation,[],[f34])).
% 11.90/1.99  
% 11.90/1.99  fof(f54,plain,(
% 11.90/1.99    ! [X5,X4,X3,X2,X1,X0,X6] : ((sP0(X5,X4,X3,X2,X1,X0,X6) | ? [X7] : (((X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7) | ~r2_hidden(X7,X6)) & ((X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7) | r2_hidden(X7,X6)))) & (! [X7] : ((r2_hidden(X7,X6) | (X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)) & ((X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7) | ~r2_hidden(X7,X6))) | ~sP0(X5,X4,X3,X2,X1,X0,X6)))),
% 11.90/1.99    inference(nnf_transformation,[],[f46])).
% 11.90/1.99  
% 11.90/1.99  fof(f55,plain,(
% 11.90/1.99    ! [X5,X4,X3,X2,X1,X0,X6] : ((sP0(X5,X4,X3,X2,X1,X0,X6) | ? [X7] : (((X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7) | ~r2_hidden(X7,X6)) & (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | r2_hidden(X7,X6)))) & (! [X7] : ((r2_hidden(X7,X6) | (X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)) & (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | ~r2_hidden(X7,X6))) | ~sP0(X5,X4,X3,X2,X1,X0,X6)))),
% 11.90/1.99    inference(flattening,[],[f54])).
% 11.90/1.99  
% 11.90/1.99  fof(f56,plain,(
% 11.90/1.99    ! [X0,X1,X2,X3,X4,X5,X6] : ((sP0(X0,X1,X2,X3,X4,X5,X6) | ? [X7] : (((X0 != X7 & X1 != X7 & X2 != X7 & X3 != X7 & X4 != X7 & X5 != X7) | ~r2_hidden(X7,X6)) & (X0 = X7 | X1 = X7 | X2 = X7 | X3 = X7 | X4 = X7 | X5 = X7 | r2_hidden(X7,X6)))) & (! [X8] : ((r2_hidden(X8,X6) | (X0 != X8 & X1 != X8 & X2 != X8 & X3 != X8 & X4 != X8 & X5 != X8)) & (X0 = X8 | X1 = X8 | X2 = X8 | X3 = X8 | X4 = X8 | X5 = X8 | ~r2_hidden(X8,X6))) | ~sP0(X0,X1,X2,X3,X4,X5,X6)))),
% 11.90/1.99    inference(rectify,[],[f55])).
% 11.90/1.99  
% 11.90/1.99  fof(f57,plain,(
% 11.90/1.99    ! [X6,X5,X4,X3,X2,X1,X0] : (? [X7] : (((X0 != X7 & X1 != X7 & X2 != X7 & X3 != X7 & X4 != X7 & X5 != X7) | ~r2_hidden(X7,X6)) & (X0 = X7 | X1 = X7 | X2 = X7 | X3 = X7 | X4 = X7 | X5 = X7 | r2_hidden(X7,X6))) => (((sK1(X0,X1,X2,X3,X4,X5,X6) != X0 & sK1(X0,X1,X2,X3,X4,X5,X6) != X1 & sK1(X0,X1,X2,X3,X4,X5,X6) != X2 & sK1(X0,X1,X2,X3,X4,X5,X6) != X3 & sK1(X0,X1,X2,X3,X4,X5,X6) != X4 & sK1(X0,X1,X2,X3,X4,X5,X6) != X5) | ~r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6),X6)) & (sK1(X0,X1,X2,X3,X4,X5,X6) = X0 | sK1(X0,X1,X2,X3,X4,X5,X6) = X1 | sK1(X0,X1,X2,X3,X4,X5,X6) = X2 | sK1(X0,X1,X2,X3,X4,X5,X6) = X3 | sK1(X0,X1,X2,X3,X4,X5,X6) = X4 | sK1(X0,X1,X2,X3,X4,X5,X6) = X5 | r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6),X6))))),
% 11.90/1.99    introduced(choice_axiom,[])).
% 11.90/1.99  
% 11.90/1.99  fof(f58,plain,(
% 11.90/1.99    ! [X0,X1,X2,X3,X4,X5,X6] : ((sP0(X0,X1,X2,X3,X4,X5,X6) | (((sK1(X0,X1,X2,X3,X4,X5,X6) != X0 & sK1(X0,X1,X2,X3,X4,X5,X6) != X1 & sK1(X0,X1,X2,X3,X4,X5,X6) != X2 & sK1(X0,X1,X2,X3,X4,X5,X6) != X3 & sK1(X0,X1,X2,X3,X4,X5,X6) != X4 & sK1(X0,X1,X2,X3,X4,X5,X6) != X5) | ~r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6),X6)) & (sK1(X0,X1,X2,X3,X4,X5,X6) = X0 | sK1(X0,X1,X2,X3,X4,X5,X6) = X1 | sK1(X0,X1,X2,X3,X4,X5,X6) = X2 | sK1(X0,X1,X2,X3,X4,X5,X6) = X3 | sK1(X0,X1,X2,X3,X4,X5,X6) = X4 | sK1(X0,X1,X2,X3,X4,X5,X6) = X5 | r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6),X6)))) & (! [X8] : ((r2_hidden(X8,X6) | (X0 != X8 & X1 != X8 & X2 != X8 & X3 != X8 & X4 != X8 & X5 != X8)) & (X0 = X8 | X1 = X8 | X2 = X8 | X3 = X8 | X4 = X8 | X5 = X8 | ~r2_hidden(X8,X6))) | ~sP0(X0,X1,X2,X3,X4,X5,X6)))),
% 11.90/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f56,f57])).
% 11.90/1.99  
% 11.90/1.99  fof(f83,plain,(
% 11.90/1.99    ( ! [X6,X4,X2,X0,X8,X5,X3,X1] : (r2_hidden(X8,X6) | X4 != X8 | ~sP0(X0,X1,X2,X3,X4,X5,X6)) )),
% 11.90/1.99    inference(cnf_transformation,[],[f58])).
% 11.90/1.99  
% 11.90/1.99  fof(f141,plain,(
% 11.90/1.99    ( ! [X6,X2,X0,X8,X5,X3,X1] : (r2_hidden(X8,X6) | ~sP0(X0,X1,X2,X3,X8,X5,X6)) )),
% 11.90/1.99    inference(equality_resolution,[],[f83])).
% 11.90/1.99  
% 11.90/1.99  fof(f22,axiom,(
% 11.90/1.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)))),
% 11.90/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.90/1.99  
% 11.90/1.99  fof(f38,plain,(
% 11.90/1.99    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 11.90/1.99    inference(ennf_transformation,[],[f22])).
% 11.90/1.99  
% 11.90/1.99  fof(f39,plain,(
% 11.90/1.99    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 11.90/1.99    inference(flattening,[],[f38])).
% 11.90/1.99  
% 11.90/1.99  fof(f108,plain,(
% 11.90/1.99    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 11.90/1.99    inference(cnf_transformation,[],[f39])).
% 11.90/1.99  
% 11.90/1.99  fof(f128,plain,(
% 11.90/1.99    ( ! [X0,X1] : (k6_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 11.90/1.99    inference(definition_unfolding,[],[f108,f121])).
% 11.90/1.99  
% 11.90/1.99  fof(f112,plain,(
% 11.90/1.99    v1_funct_1(sK5)),
% 11.90/1.99    inference(cnf_transformation,[],[f63])).
% 11.90/1.99  
% 11.90/1.99  fof(f15,axiom,(
% 11.90/1.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 11.90/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.90/1.99  
% 11.90/1.99  fof(f32,plain,(
% 11.90/1.99    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 11.90/1.99    inference(ennf_transformation,[],[f15])).
% 11.90/1.99  
% 11.90/1.99  fof(f100,plain,(
% 11.90/1.99    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 11.90/1.99    inference(cnf_transformation,[],[f32])).
% 11.90/1.99  
% 11.90/1.99  fof(f127,plain,(
% 11.90/1.99    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 11.90/1.99    inference(definition_unfolding,[],[f100,f121])).
% 11.90/1.99  
% 11.90/1.99  fof(f21,axiom,(
% 11.90/1.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 11.90/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.90/1.99  
% 11.90/1.99  fof(f36,plain,(
% 11.90/1.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 11.90/1.99    inference(ennf_transformation,[],[f21])).
% 11.90/1.99  
% 11.90/1.99  fof(f37,plain,(
% 11.90/1.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 11.90/1.99    inference(flattening,[],[f36])).
% 11.90/1.99  
% 11.90/1.99  fof(f107,plain,(
% 11.90/1.99    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.90/1.99    inference(cnf_transformation,[],[f37])).
% 11.90/1.99  
% 11.90/1.99  fof(f19,axiom,(
% 11.90/1.99    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 11.90/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.90/1.99  
% 11.90/1.99  fof(f35,plain,(
% 11.90/1.99    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 11.90/1.99    inference(ennf_transformation,[],[f19])).
% 11.90/1.99  
% 11.90/1.99  fof(f105,plain,(
% 11.90/1.99    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 11.90/1.99    inference(cnf_transformation,[],[f35])).
% 11.90/1.99  
% 11.90/1.99  fof(f25,axiom,(
% 11.90/1.99    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 11.90/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.90/1.99  
% 11.90/1.99  fof(f42,plain,(
% 11.90/1.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 11.90/1.99    inference(ennf_transformation,[],[f25])).
% 11.90/1.99  
% 11.90/1.99  fof(f43,plain,(
% 11.90/1.99    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 11.90/1.99    inference(flattening,[],[f42])).
% 11.90/1.99  
% 11.90/1.99  fof(f111,plain,(
% 11.90/1.99    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 11.90/1.99    inference(cnf_transformation,[],[f43])).
% 11.90/1.99  
% 11.90/1.99  fof(f1,axiom,(
% 11.90/1.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.90/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.90/1.99  
% 11.90/1.99  fof(f48,plain,(
% 11.90/1.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.90/1.99    inference(nnf_transformation,[],[f1])).
% 11.90/1.99  
% 11.90/1.99  fof(f49,plain,(
% 11.90/1.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.90/1.99    inference(flattening,[],[f48])).
% 11.90/1.99  
% 11.90/1.99  fof(f65,plain,(
% 11.90/1.99    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 11.90/1.99    inference(cnf_transformation,[],[f49])).
% 11.90/1.99  
% 11.90/1.99  fof(f131,plain,(
% 11.90/1.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.90/1.99    inference(equality_resolution,[],[f65])).
% 11.90/1.99  
% 11.90/1.99  fof(f11,axiom,(
% 11.90/1.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 11.90/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.90/1.99  
% 11.90/1.99  fof(f52,plain,(
% 11.90/1.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 11.90/1.99    inference(nnf_transformation,[],[f11])).
% 11.90/1.99  
% 11.90/1.99  fof(f53,plain,(
% 11.90/1.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 11.90/1.99    inference(flattening,[],[f52])).
% 11.90/1.99  
% 11.90/1.99  fof(f79,plain,(
% 11.90/1.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 11.90/1.99    inference(cnf_transformation,[],[f53])).
% 11.90/1.99  
% 11.90/1.99  fof(f136,plain,(
% 11.90/1.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 11.90/1.99    inference(equality_resolution,[],[f79])).
% 11.90/1.99  
% 11.90/1.99  fof(f2,axiom,(
% 11.90/1.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 11.90/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.90/1.99  
% 11.90/1.99  fof(f67,plain,(
% 11.90/1.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 11.90/1.99    inference(cnf_transformation,[],[f2])).
% 11.90/1.99  
% 11.90/1.99  fof(f66,plain,(
% 11.90/1.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.90/1.99    inference(cnf_transformation,[],[f49])).
% 11.90/1.99  
% 11.90/1.99  fof(f20,axiom,(
% 11.90/1.99    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 11.90/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.90/1.99  
% 11.90/1.99  fof(f106,plain,(
% 11.90/1.99    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 11.90/1.99    inference(cnf_transformation,[],[f20])).
% 11.90/1.99  
% 11.90/1.99  cnf(c_43,negated_conjecture,
% 11.90/1.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) ),
% 11.90/1.99      inference(cnf_transformation,[],[f130]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_6318,plain,
% 11.90/1.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) = iProver_top ),
% 11.90/1.99      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_38,plain,
% 11.90/1.99      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 11.90/1.99      inference(cnf_transformation,[],[f109]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_6322,plain,
% 11.90/1.99      ( v4_relat_1(X0,X1) = iProver_top
% 11.90/1.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 11.90/1.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_7506,plain,
% 11.90/1.99      ( v4_relat_1(sK5,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
% 11.90/1.99      inference(superposition,[status(thm)],[c_6318,c_6322]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_31,plain,
% 11.90/1.99      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 11.90/1.99      inference(cnf_transformation,[],[f101]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_6327,plain,
% 11.90/1.99      ( v4_relat_1(X0,X1) != iProver_top
% 11.90/1.99      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 11.90/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.90/1.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_6,plain,
% 11.90/1.99      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
% 11.90/1.99      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
% 11.90/1.99      | k1_xboole_0 = X0 ),
% 11.90/1.99      inference(cnf_transformation,[],[f124]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_6348,plain,
% 11.90/1.99      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
% 11.90/1.99      | k1_xboole_0 = X1
% 11.90/1.99      | r1_tarski(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
% 11.90/1.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_11336,plain,
% 11.90/1.99      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_relat_1(X1)
% 11.90/1.99      | k1_relat_1(X1) = k1_xboole_0
% 11.90/1.99      | v4_relat_1(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top
% 11.90/1.99      | v1_relat_1(X1) != iProver_top ),
% 11.90/1.99      inference(superposition,[status(thm)],[c_6327,c_6348]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_39684,plain,
% 11.90/1.99      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_relat_1(sK5)
% 11.90/1.99      | k1_relat_1(sK5) = k1_xboole_0
% 11.90/1.99      | v1_relat_1(sK5) != iProver_top ),
% 11.90/1.99      inference(superposition,[status(thm)],[c_7506,c_11336]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_27,plain,
% 11.90/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 11.90/1.99      inference(cnf_transformation,[],[f97]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_6330,plain,
% 11.90/1.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.90/1.99      | r1_tarski(X0,X1) = iProver_top ),
% 11.90/1.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_6853,plain,
% 11.90/1.99      ( r1_tarski(sK5,k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = iProver_top ),
% 11.90/1.99      inference(superposition,[status(thm)],[c_6318,c_6330]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_28,plain,
% 11.90/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 11.90/1.99      inference(cnf_transformation,[],[f99]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_26,plain,
% 11.90/1.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.90/1.99      inference(cnf_transformation,[],[f98]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_312,plain,
% 11.90/1.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 11.90/1.99      inference(prop_impl,[status(thm)],[c_26]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_313,plain,
% 11.90/1.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.90/1.99      inference(renaming,[status(thm)],[c_312]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_388,plain,
% 11.90/1.99      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 11.90/1.99      inference(bin_hyper_res,[status(thm)],[c_28,c_313]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_6317,plain,
% 11.90/1.99      ( r1_tarski(X0,X1) != iProver_top
% 11.90/1.99      | v1_relat_1(X1) != iProver_top
% 11.90/1.99      | v1_relat_1(X0) = iProver_top ),
% 11.90/1.99      inference(predicate_to_equality,[status(thm)],[c_388]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_6997,plain,
% 11.90/1.99      ( v1_relat_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != iProver_top
% 11.90/1.99      | v1_relat_1(sK5) = iProver_top ),
% 11.90/1.99      inference(superposition,[status(thm)],[c_6853,c_6317]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_32,plain,
% 11.90/1.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 11.90/1.99      inference(cnf_transformation,[],[f103]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_6326,plain,
% 11.90/1.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 11.90/1.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_7002,plain,
% 11.90/1.99      ( v1_relat_1(sK5) = iProver_top ),
% 11.90/1.99      inference(forward_subsumption_resolution,[status(thm)],[c_6997,c_6326]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_42531,plain,
% 11.90/1.99      ( k1_relat_1(sK5) = k1_xboole_0
% 11.90/1.99      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_relat_1(sK5) ),
% 11.90/1.99      inference(global_propositional_subsumption,
% 11.90/1.99                [status(thm)],
% 11.90/1.99                [c_39684,c_7002]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_42532,plain,
% 11.90/1.99      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_relat_1(sK5)
% 11.90/1.99      | k1_relat_1(sK5) = k1_xboole_0 ),
% 11.90/1.99      inference(renaming,[status(thm)],[c_42531]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_25,plain,
% 11.90/1.99      ( sP0(X0,X1,X2,X3,X4,X5,k6_enumset1(X5,X5,X5,X4,X3,X2,X1,X0)) ),
% 11.90/1.99      inference(cnf_transformation,[],[f143]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_6332,plain,
% 11.90/1.99      ( sP0(X0,X1,X2,X3,X4,X5,k6_enumset1(X5,X5,X5,X4,X3,X2,X1,X0)) = iProver_top ),
% 11.90/1.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_42544,plain,
% 11.90/1.99      ( k1_relat_1(sK5) = k1_xboole_0
% 11.90/1.99      | sP0(sK2,sK2,sK2,sK2,sK2,sK2,k1_relat_1(sK5)) = iProver_top ),
% 11.90/1.99      inference(superposition,[status(thm)],[c_42532,c_6332]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_41,negated_conjecture,
% 11.90/1.99      ( ~ r1_tarski(k7_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK5,sK4),k6_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2))) ),
% 11.90/1.99      inference(cnf_transformation,[],[f129]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_39,plain,
% 11.90/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.90/1.99      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 11.90/1.99      inference(cnf_transformation,[],[f110]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_6736,plain,
% 11.90/1.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))
% 11.90/1.99      | k7_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK5,X0) = k9_relat_1(sK5,X0) ),
% 11.90/1.99      inference(instantiation,[status(thm)],[c_39]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_6828,plain,
% 11.90/1.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))
% 11.90/1.99      | k7_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK5,sK4) = k9_relat_1(sK5,sK4) ),
% 11.90/1.99      inference(instantiation,[status(thm)],[c_6736]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_7003,plain,
% 11.90/1.99      ( v1_relat_1(sK5) ),
% 11.90/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_7002]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_33,plain,
% 11.90/1.99      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 11.90/1.99      inference(cnf_transformation,[],[f104]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_9528,plain,
% 11.90/1.99      ( r1_tarski(k9_relat_1(sK5,X0),k2_relat_1(sK5)) | ~ v1_relat_1(sK5) ),
% 11.90/1.99      inference(instantiation,[status(thm)],[c_33]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_13832,plain,
% 11.90/1.99      ( r1_tarski(k9_relat_1(sK5,sK4),k2_relat_1(sK5)) | ~ v1_relat_1(sK5) ),
% 11.90/1.99      inference(instantiation,[status(thm)],[c_9528]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_5444,plain,
% 11.90/1.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.90/1.99      theory(equality) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_6724,plain,
% 11.90/1.99      ( ~ r1_tarski(X0,X1)
% 11.90/1.99      | r1_tarski(k7_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK5,sK4),k6_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2)))
% 11.90/1.99      | k6_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2)) != X1
% 11.90/1.99      | k7_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK5,sK4) != X0 ),
% 11.90/1.99      inference(instantiation,[status(thm)],[c_5444]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_6827,plain,
% 11.90/1.99      ( r1_tarski(k7_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK5,sK4),k6_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2)))
% 11.90/1.99      | ~ r1_tarski(k9_relat_1(sK5,sK4),X0)
% 11.90/1.99      | k6_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2)) != X0
% 11.90/1.99      | k7_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK5,sK4) != k9_relat_1(sK5,sK4) ),
% 11.90/1.99      inference(instantiation,[status(thm)],[c_6724]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_13835,plain,
% 11.90/1.99      ( r1_tarski(k7_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK5,sK4),k6_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2)))
% 11.90/1.99      | ~ r1_tarski(k9_relat_1(sK5,sK4),k2_relat_1(sK5))
% 11.90/1.99      | k6_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2)) != k2_relat_1(sK5)
% 11.90/1.99      | k7_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK5,sK4) != k9_relat_1(sK5,sK4) ),
% 11.90/1.99      inference(instantiation,[status(thm)],[c_6827]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_21,plain,
% 11.90/1.99      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6) | r2_hidden(X4,X6) ),
% 11.90/1.99      inference(cnf_transformation,[],[f141]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_6336,plain,
% 11.90/1.99      ( sP0(X0,X1,X2,X3,X4,X5,X6) != iProver_top
% 11.90/1.99      | r2_hidden(X4,X6) = iProver_top ),
% 11.90/1.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_10626,plain,
% 11.90/1.99      ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X0,X2,X3,X4,X5)) = iProver_top ),
% 11.90/1.99      inference(superposition,[status(thm)],[c_6332,c_6336]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_42552,plain,
% 11.90/1.99      ( k1_relat_1(sK5) = k1_xboole_0
% 11.90/1.99      | r2_hidden(sK2,k1_relat_1(sK5)) = iProver_top ),
% 11.90/1.99      inference(superposition,[status(thm)],[c_42532,c_10626]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_37,plain,
% 11.90/1.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 11.90/1.99      | ~ v1_funct_1(X1)
% 11.90/1.99      | ~ v1_relat_1(X1)
% 11.90/1.99      | k6_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ),
% 11.90/1.99      inference(cnf_transformation,[],[f128]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_44,negated_conjecture,
% 11.90/1.99      ( v1_funct_1(sK5) ),
% 11.90/1.99      inference(cnf_transformation,[],[f112]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_522,plain,
% 11.90/1.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 11.90/1.99      | ~ v1_relat_1(X1)
% 11.90/1.99      | k6_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
% 11.90/1.99      | sK5 != X1 ),
% 11.90/1.99      inference(resolution_lifted,[status(thm)],[c_37,c_44]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_523,plain,
% 11.90/1.99      ( ~ r2_hidden(X0,k1_relat_1(sK5))
% 11.90/1.99      | ~ v1_relat_1(sK5)
% 11.90/1.99      | k6_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k11_relat_1(sK5,X0) ),
% 11.90/1.99      inference(unflattening,[status(thm)],[c_522]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_6316,plain,
% 11.90/1.99      ( k6_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k11_relat_1(sK5,X0)
% 11.90/1.99      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 11.90/1.99      | v1_relat_1(sK5) != iProver_top ),
% 11.90/1.99      inference(predicate_to_equality,[status(thm)],[c_523]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_45036,plain,
% 11.90/1.99      ( k6_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2)) = k11_relat_1(sK5,sK2)
% 11.90/1.99      | k1_relat_1(sK5) = k1_xboole_0
% 11.90/1.99      | v1_relat_1(sK5) != iProver_top ),
% 11.90/1.99      inference(superposition,[status(thm)],[c_42552,c_6316]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_29,plain,
% 11.90/1.99      ( ~ v1_relat_1(X0)
% 11.90/1.99      | k9_relat_1(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
% 11.90/1.99      inference(cnf_transformation,[],[f127]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_6329,plain,
% 11.90/1.99      ( k9_relat_1(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k11_relat_1(X0,X1)
% 11.90/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.90/1.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_10326,plain,
% 11.90/1.99      ( k9_relat_1(sK5,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k11_relat_1(sK5,X0) ),
% 11.90/1.99      inference(superposition,[status(thm)],[c_7002,c_6329]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_36,plain,
% 11.90/1.99      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 11.90/1.99      inference(cnf_transformation,[],[f107]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_6323,plain,
% 11.90/1.99      ( k7_relat_1(X0,X1) = X0
% 11.90/1.99      | v4_relat_1(X0,X1) != iProver_top
% 11.90/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.90/1.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_10512,plain,
% 11.90/1.99      ( k7_relat_1(sK5,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = sK5
% 11.90/1.99      | v1_relat_1(sK5) != iProver_top ),
% 11.90/1.99      inference(superposition,[status(thm)],[c_7506,c_6323]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_10883,plain,
% 11.90/1.99      ( k7_relat_1(sK5,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = sK5 ),
% 11.90/1.99      inference(global_propositional_subsumption,
% 11.90/1.99                [status(thm)],
% 11.90/1.99                [c_10512,c_7002]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_34,plain,
% 11.90/1.99      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 11.90/1.99      inference(cnf_transformation,[],[f105]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_6324,plain,
% 11.90/1.99      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 11.90/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.90/1.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_7126,plain,
% 11.90/1.99      ( k2_relat_1(k7_relat_1(sK5,X0)) = k9_relat_1(sK5,X0) ),
% 11.90/1.99      inference(superposition,[status(thm)],[c_7002,c_6324]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_10890,plain,
% 11.90/1.99      ( k9_relat_1(sK5,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = k2_relat_1(sK5) ),
% 11.90/1.99      inference(superposition,[status(thm)],[c_10883,c_7126]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_13725,plain,
% 11.90/1.99      ( k11_relat_1(sK5,sK2) = k2_relat_1(sK5) ),
% 11.90/1.99      inference(superposition,[status(thm)],[c_10326,c_10890]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_45040,plain,
% 11.90/1.99      ( k6_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2)) = k2_relat_1(sK5)
% 11.90/1.99      | k1_relat_1(sK5) = k1_xboole_0
% 11.90/1.99      | v1_relat_1(sK5) != iProver_top ),
% 11.90/1.99      inference(light_normalisation,[status(thm)],[c_45036,c_13725]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_45074,plain,
% 11.90/1.99      ( k1_relat_1(sK5) = k1_xboole_0 ),
% 11.90/1.99      inference(global_propositional_subsumption,
% 11.90/1.99                [status(thm)],
% 11.90/1.99                [c_42544,c_43,c_41,c_6828,c_7002,c_7003,c_13832,c_13835,
% 11.90/1.99                 c_45040]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_42551,plain,
% 11.90/1.99      ( k1_relat_1(sK5) = k1_xboole_0
% 11.90/1.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),sK3))) = iProver_top ),
% 11.90/1.99      inference(superposition,[status(thm)],[c_42532,c_6318]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_46,plain,
% 11.90/1.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) = iProver_top ),
% 11.90/1.99      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_40,plain,
% 11.90/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.90/1.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 11.90/1.99      | ~ r1_tarski(k1_relat_1(X0),X3) ),
% 11.90/1.99      inference(cnf_transformation,[],[f111]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_6707,plain,
% 11.90/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.90/1.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X2)))
% 11.90/1.99      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) ),
% 11.90/1.99      inference(instantiation,[status(thm)],[c_40]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_7475,plain,
% 11.90/1.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))
% 11.90/1.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),sK3)))
% 11.90/1.99      | ~ r1_tarski(k1_relat_1(sK5),k1_relat_1(sK5)) ),
% 11.90/1.99      inference(instantiation,[status(thm)],[c_6707]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_7476,plain,
% 11.90/1.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) != iProver_top
% 11.90/1.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),sK3))) = iProver_top
% 11.90/1.99      | r1_tarski(k1_relat_1(sK5),k1_relat_1(sK5)) != iProver_top ),
% 11.90/1.99      inference(predicate_to_equality,[status(thm)],[c_7475]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_1,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f131]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_6708,plain,
% 11.90/1.99      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) ),
% 11.90/1.99      inference(instantiation,[status(thm)],[c_1]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_7860,plain,
% 11.90/1.99      ( r1_tarski(k1_relat_1(sK5),k1_relat_1(sK5)) ),
% 11.90/1.99      inference(instantiation,[status(thm)],[c_6708]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_7861,plain,
% 11.90/1.99      ( r1_tarski(k1_relat_1(sK5),k1_relat_1(sK5)) = iProver_top ),
% 11.90/1.99      inference(predicate_to_equality,[status(thm)],[c_7860]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_42642,plain,
% 11.90/1.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),sK3))) = iProver_top ),
% 11.90/1.99      inference(global_propositional_subsumption,
% 11.90/1.99                [status(thm)],
% 11.90/1.99                [c_42551,c_46,c_7476,c_7861]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_42647,plain,
% 11.90/1.99      ( r1_tarski(sK5,k2_zfmisc_1(k1_relat_1(sK5),sK3)) = iProver_top ),
% 11.90/1.99      inference(superposition,[status(thm)],[c_42642,c_6330]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_45078,plain,
% 11.90/1.99      ( r1_tarski(sK5,k2_zfmisc_1(k1_xboole_0,sK3)) = iProver_top ),
% 11.90/1.99      inference(demodulation,[status(thm)],[c_45074,c_42647]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_8,plain,
% 11.90/1.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 11.90/1.99      inference(cnf_transformation,[],[f136]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_46062,plain,
% 11.90/1.99      ( r1_tarski(sK5,k1_xboole_0) = iProver_top ),
% 11.90/1.99      inference(demodulation,[status(thm)],[c_45078,c_8]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_3,plain,
% 11.90/1.99      ( r1_tarski(k1_xboole_0,X0) ),
% 11.90/1.99      inference(cnf_transformation,[],[f67]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_6351,plain,
% 11.90/1.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 11.90/1.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_0,plain,
% 11.90/1.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 11.90/1.99      inference(cnf_transformation,[],[f66]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_6353,plain,
% 11.90/1.99      ( X0 = X1
% 11.90/1.99      | r1_tarski(X0,X1) != iProver_top
% 11.90/1.99      | r1_tarski(X1,X0) != iProver_top ),
% 11.90/1.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_9813,plain,
% 11.90/1.99      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 11.90/1.99      inference(superposition,[status(thm)],[c_6351,c_6353]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_49156,plain,
% 11.90/1.99      ( sK5 = k1_xboole_0 ),
% 11.90/1.99      inference(superposition,[status(thm)],[c_46062,c_9813]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_6321,plain,
% 11.90/1.99      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 11.90/1.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.90/1.99      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_10650,plain,
% 11.90/1.99      ( k7_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK5,X0) = k9_relat_1(sK5,X0) ),
% 11.90/1.99      inference(superposition,[status(thm)],[c_6318,c_6321]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_6319,plain,
% 11.90/1.99      ( r1_tarski(k7_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK5,sK4),k6_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2))) != iProver_top ),
% 11.90/1.99      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 11.90/1.99  
% 11.90/1.99  cnf(c_10787,plain,
% 11.90/1.99      ( r1_tarski(k9_relat_1(sK5,sK4),k6_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2))) != iProver_top ),
% 11.90/2.00      inference(demodulation,[status(thm)],[c_10650,c_6319]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_54567,plain,
% 11.90/2.00      ( r1_tarski(k9_relat_1(k1_xboole_0,sK4),k6_enumset1(k1_funct_1(k1_xboole_0,sK2),k1_funct_1(k1_xboole_0,sK2),k1_funct_1(k1_xboole_0,sK2),k1_funct_1(k1_xboole_0,sK2),k1_funct_1(k1_xboole_0,sK2),k1_funct_1(k1_xboole_0,sK2),k1_funct_1(k1_xboole_0,sK2),k1_funct_1(k1_xboole_0,sK2))) != iProver_top ),
% 11.90/2.00      inference(demodulation,[status(thm)],[c_49156,c_10787]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_35,plain,
% 11.90/2.00      ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 11.90/2.00      inference(cnf_transformation,[],[f106]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_54611,plain,
% 11.90/2.00      ( r1_tarski(k1_xboole_0,k6_enumset1(k1_funct_1(k1_xboole_0,sK2),k1_funct_1(k1_xboole_0,sK2),k1_funct_1(k1_xboole_0,sK2),k1_funct_1(k1_xboole_0,sK2),k1_funct_1(k1_xboole_0,sK2),k1_funct_1(k1_xboole_0,sK2),k1_funct_1(k1_xboole_0,sK2),k1_funct_1(k1_xboole_0,sK2))) != iProver_top ),
% 11.90/2.00      inference(demodulation,[status(thm)],[c_54567,c_35]) ).
% 11.90/2.00  
% 11.90/2.00  cnf(c_54733,plain,
% 11.90/2.00      ( $false ),
% 11.90/2.00      inference(forward_subsumption_resolution,[status(thm)],[c_54611,c_6351]) ).
% 11.90/2.00  
% 11.90/2.00  
% 11.90/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.90/2.00  
% 11.90/2.00  ------                               Statistics
% 11.90/2.00  
% 11.90/2.00  ------ General
% 11.90/2.00  
% 11.90/2.00  abstr_ref_over_cycles:                  0
% 11.90/2.00  abstr_ref_under_cycles:                 0
% 11.90/2.00  gc_basic_clause_elim:                   0
% 11.90/2.00  forced_gc_time:                         0
% 11.90/2.00  parsing_time:                           0.011
% 11.90/2.00  unif_index_cands_time:                  0.
% 11.90/2.00  unif_index_add_time:                    0.
% 11.90/2.00  orderings_time:                         0.
% 11.90/2.00  out_proof_time:                         0.014
% 11.90/2.00  total_time:                             1.411
% 11.90/2.00  num_of_symbols:                         54
% 11.90/2.00  num_of_terms:                           51019
% 11.90/2.00  
% 11.90/2.00  ------ Preprocessing
% 11.90/2.00  
% 11.90/2.00  num_of_splits:                          0
% 11.90/2.00  num_of_split_atoms:                     0
% 11.90/2.00  num_of_reused_defs:                     0
% 11.90/2.00  num_eq_ax_congr_red:                    56
% 11.90/2.00  num_of_sem_filtered_clauses:            1
% 11.90/2.00  num_of_subtypes:                        0
% 11.90/2.00  monotx_restored_types:                  0
% 11.90/2.00  sat_num_of_epr_types:                   0
% 11.90/2.00  sat_num_of_non_cyclic_types:            0
% 11.90/2.00  sat_guarded_non_collapsed_types:        0
% 11.90/2.00  num_pure_diseq_elim:                    0
% 11.90/2.00  simp_replaced_by:                       0
% 11.90/2.00  res_preprocessed:                       206
% 11.90/2.00  prep_upred:                             0
% 11.90/2.00  prep_unflattend:                        313
% 11.90/2.00  smt_new_axioms:                         0
% 11.90/2.00  pred_elim_cands:                        6
% 11.90/2.00  pred_elim:                              1
% 11.90/2.00  pred_elim_cl:                           1
% 11.90/2.00  pred_elim_cycles:                       7
% 11.90/2.00  merged_defs:                            8
% 11.90/2.00  merged_defs_ncl:                        0
% 11.90/2.00  bin_hyper_res:                          9
% 11.90/2.00  prep_cycles:                            4
% 11.90/2.00  pred_elim_time:                         0.066
% 11.90/2.00  splitting_time:                         0.
% 11.90/2.00  sem_filter_time:                        0.
% 11.90/2.00  monotx_time:                            0.001
% 11.90/2.00  subtype_inf_time:                       0.
% 11.90/2.00  
% 11.90/2.00  ------ Problem properties
% 11.90/2.00  
% 11.90/2.00  clauses:                                43
% 11.90/2.00  conjectures:                            3
% 11.90/2.00  epr:                                    12
% 11.90/2.00  horn:                                   39
% 11.90/2.00  ground:                                 3
% 11.90/2.00  unary:                                  12
% 11.90/2.00  binary:                                 14
% 11.90/2.00  lits:                                   101
% 11.90/2.00  lits_eq:                                34
% 11.90/2.00  fd_pure:                                0
% 11.90/2.00  fd_pseudo:                              0
% 11.90/2.00  fd_cond:                                1
% 11.90/2.00  fd_pseudo_cond:                         4
% 11.90/2.00  ac_symbols:                             0
% 11.90/2.00  
% 11.90/2.00  ------ Propositional Solver
% 11.90/2.00  
% 11.90/2.00  prop_solver_calls:                      28
% 11.90/2.00  prop_fast_solver_calls:                 2921
% 11.90/2.00  smt_solver_calls:                       0
% 11.90/2.00  smt_fast_solver_calls:                  0
% 11.90/2.00  prop_num_of_clauses:                    10565
% 11.90/2.00  prop_preprocess_simplified:             26138
% 11.90/2.00  prop_fo_subsumed:                       41
% 11.90/2.00  prop_solver_time:                       0.
% 11.90/2.00  smt_solver_time:                        0.
% 11.90/2.00  smt_fast_solver_time:                   0.
% 11.90/2.00  prop_fast_solver_time:                  0.
% 11.90/2.00  prop_unsat_core_time:                   0.
% 11.90/2.00  
% 11.90/2.00  ------ QBF
% 11.90/2.00  
% 11.90/2.00  qbf_q_res:                              0
% 11.90/2.00  qbf_num_tautologies:                    0
% 11.90/2.00  qbf_prep_cycles:                        0
% 11.90/2.00  
% 11.90/2.00  ------ BMC1
% 11.90/2.00  
% 11.90/2.00  bmc1_current_bound:                     -1
% 11.90/2.00  bmc1_last_solved_bound:                 -1
% 11.90/2.00  bmc1_unsat_core_size:                   -1
% 11.90/2.00  bmc1_unsat_core_parents_size:           -1
% 11.90/2.00  bmc1_merge_next_fun:                    0
% 11.90/2.00  bmc1_unsat_core_clauses_time:           0.
% 11.90/2.00  
% 11.90/2.00  ------ Instantiation
% 11.90/2.00  
% 11.90/2.00  inst_num_of_clauses:                    2616
% 11.90/2.00  inst_num_in_passive:                    1132
% 11.90/2.00  inst_num_in_active:                     953
% 11.90/2.00  inst_num_in_unprocessed:                531
% 11.90/2.00  inst_num_of_loops:                      1090
% 11.90/2.00  inst_num_of_learning_restarts:          0
% 11.90/2.00  inst_num_moves_active_passive:          136
% 11.90/2.00  inst_lit_activity:                      0
% 11.90/2.00  inst_lit_activity_moves:                0
% 11.90/2.00  inst_num_tautologies:                   0
% 11.90/2.00  inst_num_prop_implied:                  0
% 11.90/2.00  inst_num_existing_simplified:           0
% 11.90/2.00  inst_num_eq_res_simplified:             0
% 11.90/2.00  inst_num_child_elim:                    0
% 11.90/2.00  inst_num_of_dismatching_blockings:      10862
% 11.90/2.00  inst_num_of_non_proper_insts:           2509
% 11.90/2.00  inst_num_of_duplicates:                 0
% 11.90/2.00  inst_inst_num_from_inst_to_res:         0
% 11.90/2.00  inst_dismatching_checking_time:         0.
% 11.90/2.00  
% 11.90/2.00  ------ Resolution
% 11.90/2.00  
% 11.90/2.00  res_num_of_clauses:                     0
% 11.90/2.00  res_num_in_passive:                     0
% 11.90/2.00  res_num_in_active:                      0
% 11.90/2.00  res_num_of_loops:                       210
% 11.90/2.00  res_forward_subset_subsumed:            3318
% 11.90/2.00  res_backward_subset_subsumed:           0
% 11.90/2.00  res_forward_subsumed:                   0
% 11.90/2.00  res_backward_subsumed:                  0
% 11.90/2.00  res_forward_subsumption_resolution:     0
% 11.90/2.00  res_backward_subsumption_resolution:    0
% 11.90/2.00  res_clause_to_clause_subsumption:       5001
% 11.90/2.00  res_orphan_elimination:                 0
% 11.90/2.00  res_tautology_del:                      106
% 11.90/2.00  res_num_eq_res_simplified:              0
% 11.90/2.00  res_num_sel_changes:                    0
% 11.90/2.00  res_moves_from_active_to_pass:          0
% 11.90/2.00  
% 11.90/2.00  ------ Superposition
% 11.90/2.00  
% 11.90/2.00  sup_time_total:                         0.
% 11.90/2.00  sup_time_generating:                    0.
% 11.90/2.00  sup_time_sim_full:                      0.
% 11.90/2.00  sup_time_sim_immed:                     0.
% 11.90/2.00  
% 11.90/2.00  sup_num_of_clauses:                     462
% 11.90/2.00  sup_num_in_active:                      92
% 11.90/2.00  sup_num_in_passive:                     370
% 11.90/2.00  sup_num_of_loops:                       217
% 11.90/2.00  sup_fw_superposition:                   333
% 11.90/2.00  sup_bw_superposition:                   571
% 11.90/2.00  sup_immediate_simplified:               247
% 11.90/2.00  sup_given_eliminated:                   3
% 11.90/2.00  comparisons_done:                       0
% 11.90/2.00  comparisons_avoided:                    1254
% 11.90/2.00  
% 11.90/2.00  ------ Simplifications
% 11.90/2.00  
% 11.90/2.00  
% 11.90/2.00  sim_fw_subset_subsumed:                 47
% 11.90/2.00  sim_bw_subset_subsumed:                 15
% 11.90/2.00  sim_fw_subsumed:                        104
% 11.90/2.00  sim_bw_subsumed:                        7
% 11.90/2.00  sim_fw_subsumption_res:                 3
% 11.90/2.00  sim_bw_subsumption_res:                 0
% 11.90/2.00  sim_tautology_del:                      16
% 11.90/2.00  sim_eq_tautology_del:                   50
% 11.90/2.00  sim_eq_res_simp:                        0
% 11.90/2.00  sim_fw_demodulated:                     52
% 11.90/2.00  sim_bw_demodulated:                     121
% 11.90/2.00  sim_light_normalised:                   97
% 11.90/2.00  sim_joinable_taut:                      0
% 11.90/2.00  sim_joinable_simp:                      0
% 11.90/2.00  sim_ac_normalised:                      0
% 11.90/2.00  sim_smt_subsumption:                    0
% 11.90/2.00  
%------------------------------------------------------------------------------
