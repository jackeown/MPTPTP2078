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
% DateTime   : Thu Dec  3 12:05:29 EST 2020

% Result     : Theorem 7.38s
% Output     : CNFRefutation 7.38s
% Verified   : 
% Statistics : Number of formulae       :  226 (4826 expanded)
%              Number of clauses        :  119 ( 930 expanded)
%              Number of leaves         :   28 (1205 expanded)
%              Depth                    :   32
%              Number of atoms          :  505 (9488 expanded)
%              Number of equality atoms :  246 (4472 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f58])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f125,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f81])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k1_relat_1(X1))
          | k1_xboole_0 = k11_relat_1(X1,X0) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X1))
      | k1_xboole_0 = k11_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f60])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f110,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f77,f78])).

fof(f111,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f76,f110])).

fof(f112,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f75,f111])).

fof(f113,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f74,f112])).

fof(f114,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f73,f113])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f84,f114])).

fof(f29,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f29])).

fof(f31,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(pure_predicate_removal,[],[f30])).

fof(f54,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f55,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f54])).

fof(f66,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
        & k1_xboole_0 != X1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
      & k1_xboole_0 != sK1
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f55,f66])).

fof(f107,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f67])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f115,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f72,f114])).

fof(f122,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f107,f115])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f22])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f86,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f56])).

fof(f70,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f119,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f87,f115])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f93,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f42])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f120,plain,(
    ! [X0,X1] :
      ( k6_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f97,f115,f115])).

fof(f106,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f67])).

fof(f26,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f109,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f67])).

fof(f121,plain,(
    ~ r1_tarski(k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f109,f115,f115])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f123,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f69])).

fof(f28,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_tarski(k2_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f52])).

fof(f105,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f101,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f126,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f80])).

fof(f27,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f50])).

fof(f104,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f125])).

cnf(c_16,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k11_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1745,plain,
    ( k11_relat_1(X0,X1) = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0),X1) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_1754,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_1730,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1735,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3643,plain,
    ( k1_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1730,c_1735])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1737,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4314,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3643,c_1737])).

cnf(c_36,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1983,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1984,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1983])).

cnf(c_24,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1995,plain,
    ( v4_relat_1(sK3,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_1996,plain,
    ( v4_relat_1(sK3,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1995])).

cnf(c_14,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2117,plain,
    ( ~ v4_relat_1(sK3,X0)
    | r1_tarski(k1_relat_1(sK3),X0)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2311,plain,
    ( ~ v4_relat_1(sK3,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | r1_tarski(k1_relat_1(sK3),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2117])).

cnf(c_2312,plain,
    ( v4_relat_1(sK3,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != iProver_top
    | r1_tarski(k1_relat_1(sK3),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2311])).

cnf(c_10,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2440,plain,
    ( m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(X1))
    | ~ r1_tarski(k1_relat_1(X0),X1) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_3364,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | ~ r1_tarski(k1_relat_1(sK3),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_2440])).

cnf(c_3365,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3364])).

cnf(c_4637,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4314,c_36,c_1984,c_1996,c_2312,c_3365])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1750,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4642,plain,
    ( r1_tarski(k1_relat_1(sK3),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4637,c_1750])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1757,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4972,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4642,c_1757])).

cnf(c_11932,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | r2_hidden(sK0,k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1754,c_4972])).

cnf(c_17228,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k11_relat_1(sK3,sK0) = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1745,c_11932])).

cnf(c_1739,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2545,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1730,c_1739])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_1749,plain,
    ( k9_relat_1(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k11_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_8447,plain,
    ( k9_relat_1(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k11_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_2545,c_1749])).

cnf(c_1738,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2831,plain,
    ( v4_relat_1(sK3,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1730,c_1738])).

cnf(c_18,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1743,plain,
    ( k7_relat_1(X0,X1) = X0
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5144,plain,
    ( k7_relat_1(sK3,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = sK3
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2831,c_1743])).

cnf(c_2114,plain,
    ( ~ v4_relat_1(sK3,X0)
    | ~ v1_relat_1(sK3)
    | k7_relat_1(sK3,X0) = sK3 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2300,plain,
    ( ~ v4_relat_1(sK3,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ v1_relat_1(sK3)
    | k7_relat_1(sK3,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = sK3 ),
    inference(instantiation,[status(thm)],[c_2114])).

cnf(c_5253,plain,
    ( k7_relat_1(sK3,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5144,c_33,c_1983,c_1995,c_2300])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1746,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2795,plain,
    ( k2_relat_1(k7_relat_1(sK3,X0)) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_2545,c_1746])).

cnf(c_5256,plain,
    ( k9_relat_1(sK3,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_5253,c_2795])).

cnf(c_8973,plain,
    ( k11_relat_1(sK3,sK0) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_8447,c_5256])).

cnf(c_17229,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k2_relat_1(sK3) = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_17228,c_8973])).

cnf(c_17230,plain,
    ( ~ v1_relat_1(sK3)
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k2_relat_1(sK3) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_17229])).

cnf(c_17398,plain,
    ( k2_relat_1(sK3) = k1_xboole_0
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17229,c_33,c_1983,c_17230])).

cnf(c_17399,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k2_relat_1(sK3) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_17398])).

cnf(c_22,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k1_relat_1(X0)
    | k6_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_415,plain,
    ( ~ v1_relat_1(X0)
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k1_relat_1(X0)
    | k6_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_34])).

cnf(c_416,plain,
    ( ~ v1_relat_1(sK3)
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(sK3)
    | k6_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_415])).

cnf(c_1729,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(sK3)
    | k6_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_416])).

cnf(c_417,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(sK3)
    | k6_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_416])).

cnf(c_1989,plain,
    ( k6_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1729,c_36,c_417,c_1984])).

cnf(c_1990,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(sK3)
    | k6_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
    inference(renaming,[status(thm)],[c_1989])).

cnf(c_17406,plain,
    ( k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | k2_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_17399,c_1990])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1734,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_6289,plain,
    ( k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1730,c_1734])).

cnf(c_31,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_1731,plain,
    ( r1_tarski(k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_6640,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6289,c_1731])).

cnf(c_18113,plain,
    ( k2_relat_1(sK3) = k1_xboole_0
    | r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_17406,c_6640])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_1756,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ r1_tarski(k2_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1732,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_2165,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1730,c_1732])).

cnf(c_6291,plain,
    ( k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0,sK3,X1) = k9_relat_1(sK3,X1)
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2165,c_1734])).

cnf(c_6785,plain,
    ( k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_relat_1(sK3),sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1756,c_6291])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1736,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_7854,plain,
    ( m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(k2_relat_1(sK3))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_relat_1(sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6785,c_1736])).

cnf(c_2046,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
    | ~ r1_tarski(k2_relat_1(X0),k2_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_2588,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_relat_1(sK3))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))
    | ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_2046])).

cnf(c_2589,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_relat_1(sK3)))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) != iProver_top
    | r1_tarski(k2_relat_1(sK3),k2_relat_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2588])).

cnf(c_2047,plain,
    ( r1_tarski(k2_relat_1(X0),k2_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2731,plain,
    ( r1_tarski(k2_relat_1(sK3),k2_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_2047])).

cnf(c_2732,plain,
    ( r1_tarski(k2_relat_1(sK3),k2_relat_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2731])).

cnf(c_12099,plain,
    ( m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(k2_relat_1(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7854,c_36,c_2589,c_2732])).

cnf(c_12109,plain,
    ( r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_12099,c_1750])).

cnf(c_18212,plain,
    ( k2_relat_1(sK3) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_18113,c_12109])).

cnf(c_18250,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0))) = iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_18212,c_2165])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_105,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_18471,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18250,c_105])).

cnf(c_18478,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_18471])).

cnf(c_5,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f126])).

cnf(c_6294,plain,
    ( k7_relset_1(k1_xboole_0,X0,X1,X2) = k9_relat_1(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_1734])).

cnf(c_18891,plain,
    ( k7_relset_1(k1_xboole_0,X0,sK3,X1) = k9_relat_1(sK3,X1) ),
    inference(superposition,[status(thm)],[c_18478,c_6294])).

cnf(c_3283,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k7_relset_1(X1,X2,X0,X3),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1736,c_1750])).

cnf(c_25799,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
    | r1_tarski(k9_relat_1(sK3,X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_18891,c_3283])).

cnf(c_25831,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k9_relat_1(sK3,X0),X1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_25799,c_5])).

cnf(c_2129,plain,
    ( v4_relat_1(sK3,X0) != iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2117])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_2737,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X1)))
    | ~ r1_tarski(k1_relat_1(sK3),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_2738,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X1))) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2737])).

cnf(c_3244,plain,
    ( ~ m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(X1))
    | r1_tarski(k9_relat_1(sK3,X0),X1) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_3245,plain,
    ( m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(k9_relat_1(sK3,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3244])).

cnf(c_1733,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_18484,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_18471,c_1733])).

cnf(c_2833,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_1738])).

cnf(c_18889,plain,
    ( v4_relat_1(sK3,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_18478,c_2833])).

cnf(c_18481,plain,
    ( k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0,sK3,X1) = k9_relat_1(sK3,X1) ),
    inference(superposition,[status(thm)],[c_18471,c_1734])).

cnf(c_20647,plain,
    ( m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(X1)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_18481,c_1736])).

cnf(c_26281,plain,
    ( r1_tarski(k9_relat_1(sK3,X0),X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_25831,c_36,c_1984,c_1996,c_2129,c_2312,c_2738,c_3245,c_18484,c_18889,c_20647])).

cnf(c_26299,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_26281,c_6640])).

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
% 0.13/0.34  % DateTime   : Tue Dec  1 13:38:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.38/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.38/1.49  
% 7.38/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.38/1.49  
% 7.38/1.49  ------  iProver source info
% 7.38/1.49  
% 7.38/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.38/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.38/1.49  git: non_committed_changes: false
% 7.38/1.49  git: last_make_outside_of_git: false
% 7.38/1.49  
% 7.38/1.49  ------ 
% 7.38/1.49  
% 7.38/1.49  ------ Input Options
% 7.38/1.49  
% 7.38/1.49  --out_options                           all
% 7.38/1.49  --tptp_safe_out                         true
% 7.38/1.49  --problem_path                          ""
% 7.38/1.49  --include_path                          ""
% 7.38/1.49  --clausifier                            res/vclausify_rel
% 7.38/1.49  --clausifier_options                    --mode clausify
% 7.38/1.49  --stdin                                 false
% 7.38/1.49  --stats_out                             all
% 7.38/1.49  
% 7.38/1.49  ------ General Options
% 7.38/1.49  
% 7.38/1.49  --fof                                   false
% 7.38/1.49  --time_out_real                         305.
% 7.38/1.49  --time_out_virtual                      -1.
% 7.38/1.49  --symbol_type_check                     false
% 7.38/1.49  --clausify_out                          false
% 7.38/1.49  --sig_cnt_out                           false
% 7.38/1.49  --trig_cnt_out                          false
% 7.38/1.49  --trig_cnt_out_tolerance                1.
% 7.38/1.49  --trig_cnt_out_sk_spl                   false
% 7.38/1.49  --abstr_cl_out                          false
% 7.38/1.49  
% 7.38/1.49  ------ Global Options
% 7.38/1.49  
% 7.38/1.49  --schedule                              default
% 7.38/1.49  --add_important_lit                     false
% 7.38/1.49  --prop_solver_per_cl                    1000
% 7.38/1.49  --min_unsat_core                        false
% 7.38/1.49  --soft_assumptions                      false
% 7.38/1.49  --soft_lemma_size                       3
% 7.38/1.49  --prop_impl_unit_size                   0
% 7.38/1.49  --prop_impl_unit                        []
% 7.38/1.49  --share_sel_clauses                     true
% 7.38/1.49  --reset_solvers                         false
% 7.38/1.49  --bc_imp_inh                            [conj_cone]
% 7.38/1.49  --conj_cone_tolerance                   3.
% 7.38/1.49  --extra_neg_conj                        none
% 7.38/1.49  --large_theory_mode                     true
% 7.38/1.49  --prolific_symb_bound                   200
% 7.38/1.49  --lt_threshold                          2000
% 7.38/1.49  --clause_weak_htbl                      true
% 7.38/1.49  --gc_record_bc_elim                     false
% 7.38/1.49  
% 7.38/1.49  ------ Preprocessing Options
% 7.38/1.49  
% 7.38/1.49  --preprocessing_flag                    true
% 7.38/1.49  --time_out_prep_mult                    0.1
% 7.38/1.49  --splitting_mode                        input
% 7.38/1.49  --splitting_grd                         true
% 7.38/1.49  --splitting_cvd                         false
% 7.38/1.49  --splitting_cvd_svl                     false
% 7.38/1.49  --splitting_nvd                         32
% 7.38/1.49  --sub_typing                            true
% 7.38/1.49  --prep_gs_sim                           true
% 7.38/1.49  --prep_unflatten                        true
% 7.38/1.49  --prep_res_sim                          true
% 7.38/1.49  --prep_upred                            true
% 7.38/1.49  --prep_sem_filter                       exhaustive
% 7.38/1.49  --prep_sem_filter_out                   false
% 7.38/1.49  --pred_elim                             true
% 7.38/1.49  --res_sim_input                         true
% 7.38/1.49  --eq_ax_congr_red                       true
% 7.38/1.49  --pure_diseq_elim                       true
% 7.38/1.49  --brand_transform                       false
% 7.38/1.49  --non_eq_to_eq                          false
% 7.38/1.49  --prep_def_merge                        true
% 7.38/1.49  --prep_def_merge_prop_impl              false
% 7.38/1.49  --prep_def_merge_mbd                    true
% 7.38/1.49  --prep_def_merge_tr_red                 false
% 7.38/1.49  --prep_def_merge_tr_cl                  false
% 7.38/1.49  --smt_preprocessing                     true
% 7.38/1.49  --smt_ac_axioms                         fast
% 7.38/1.49  --preprocessed_out                      false
% 7.38/1.49  --preprocessed_stats                    false
% 7.38/1.49  
% 7.38/1.49  ------ Abstraction refinement Options
% 7.38/1.49  
% 7.38/1.49  --abstr_ref                             []
% 7.38/1.49  --abstr_ref_prep                        false
% 7.38/1.49  --abstr_ref_until_sat                   false
% 7.38/1.49  --abstr_ref_sig_restrict                funpre
% 7.38/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.38/1.49  --abstr_ref_under                       []
% 7.38/1.49  
% 7.38/1.49  ------ SAT Options
% 7.38/1.49  
% 7.38/1.49  --sat_mode                              false
% 7.38/1.49  --sat_fm_restart_options                ""
% 7.38/1.49  --sat_gr_def                            false
% 7.38/1.49  --sat_epr_types                         true
% 7.38/1.49  --sat_non_cyclic_types                  false
% 7.38/1.49  --sat_finite_models                     false
% 7.38/1.49  --sat_fm_lemmas                         false
% 7.38/1.49  --sat_fm_prep                           false
% 7.38/1.49  --sat_fm_uc_incr                        true
% 7.38/1.49  --sat_out_model                         small
% 7.38/1.49  --sat_out_clauses                       false
% 7.38/1.49  
% 7.38/1.49  ------ QBF Options
% 7.38/1.49  
% 7.38/1.49  --qbf_mode                              false
% 7.38/1.49  --qbf_elim_univ                         false
% 7.38/1.49  --qbf_dom_inst                          none
% 7.38/1.49  --qbf_dom_pre_inst                      false
% 7.38/1.49  --qbf_sk_in                             false
% 7.38/1.49  --qbf_pred_elim                         true
% 7.38/1.49  --qbf_split                             512
% 7.38/1.49  
% 7.38/1.49  ------ BMC1 Options
% 7.38/1.49  
% 7.38/1.49  --bmc1_incremental                      false
% 7.38/1.49  --bmc1_axioms                           reachable_all
% 7.38/1.49  --bmc1_min_bound                        0
% 7.38/1.49  --bmc1_max_bound                        -1
% 7.38/1.49  --bmc1_max_bound_default                -1
% 7.38/1.49  --bmc1_symbol_reachability              true
% 7.38/1.49  --bmc1_property_lemmas                  false
% 7.38/1.49  --bmc1_k_induction                      false
% 7.38/1.49  --bmc1_non_equiv_states                 false
% 7.38/1.49  --bmc1_deadlock                         false
% 7.38/1.49  --bmc1_ucm                              false
% 7.38/1.49  --bmc1_add_unsat_core                   none
% 7.38/1.49  --bmc1_unsat_core_children              false
% 7.38/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.38/1.49  --bmc1_out_stat                         full
% 7.38/1.49  --bmc1_ground_init                      false
% 7.38/1.49  --bmc1_pre_inst_next_state              false
% 7.38/1.49  --bmc1_pre_inst_state                   false
% 7.38/1.49  --bmc1_pre_inst_reach_state             false
% 7.38/1.49  --bmc1_out_unsat_core                   false
% 7.38/1.49  --bmc1_aig_witness_out                  false
% 7.38/1.49  --bmc1_verbose                          false
% 7.38/1.49  --bmc1_dump_clauses_tptp                false
% 7.38/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.38/1.49  --bmc1_dump_file                        -
% 7.38/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.38/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.38/1.49  --bmc1_ucm_extend_mode                  1
% 7.38/1.49  --bmc1_ucm_init_mode                    2
% 7.38/1.49  --bmc1_ucm_cone_mode                    none
% 7.38/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.38/1.49  --bmc1_ucm_relax_model                  4
% 7.38/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.38/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.38/1.49  --bmc1_ucm_layered_model                none
% 7.38/1.49  --bmc1_ucm_max_lemma_size               10
% 7.38/1.49  
% 7.38/1.49  ------ AIG Options
% 7.38/1.49  
% 7.38/1.49  --aig_mode                              false
% 7.38/1.49  
% 7.38/1.49  ------ Instantiation Options
% 7.38/1.49  
% 7.38/1.49  --instantiation_flag                    true
% 7.38/1.49  --inst_sos_flag                         false
% 7.38/1.49  --inst_sos_phase                        true
% 7.38/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.38/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.38/1.49  --inst_lit_sel_side                     num_symb
% 7.38/1.49  --inst_solver_per_active                1400
% 7.38/1.49  --inst_solver_calls_frac                1.
% 7.38/1.49  --inst_passive_queue_type               priority_queues
% 7.38/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.38/1.49  --inst_passive_queues_freq              [25;2]
% 7.38/1.49  --inst_dismatching                      true
% 7.38/1.49  --inst_eager_unprocessed_to_passive     true
% 7.38/1.49  --inst_prop_sim_given                   true
% 7.38/1.49  --inst_prop_sim_new                     false
% 7.38/1.49  --inst_subs_new                         false
% 7.38/1.50  --inst_eq_res_simp                      false
% 7.38/1.50  --inst_subs_given                       false
% 7.38/1.50  --inst_orphan_elimination               true
% 7.38/1.50  --inst_learning_loop_flag               true
% 7.38/1.50  --inst_learning_start                   3000
% 7.38/1.50  --inst_learning_factor                  2
% 7.38/1.50  --inst_start_prop_sim_after_learn       3
% 7.38/1.50  --inst_sel_renew                        solver
% 7.38/1.50  --inst_lit_activity_flag                true
% 7.38/1.50  --inst_restr_to_given                   false
% 7.38/1.50  --inst_activity_threshold               500
% 7.38/1.50  --inst_out_proof                        true
% 7.38/1.50  
% 7.38/1.50  ------ Resolution Options
% 7.38/1.50  
% 7.38/1.50  --resolution_flag                       true
% 7.38/1.50  --res_lit_sel                           adaptive
% 7.38/1.50  --res_lit_sel_side                      none
% 7.38/1.50  --res_ordering                          kbo
% 7.38/1.50  --res_to_prop_solver                    active
% 7.38/1.50  --res_prop_simpl_new                    false
% 7.38/1.50  --res_prop_simpl_given                  true
% 7.38/1.50  --res_passive_queue_type                priority_queues
% 7.38/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.38/1.50  --res_passive_queues_freq               [15;5]
% 7.38/1.50  --res_forward_subs                      full
% 7.38/1.50  --res_backward_subs                     full
% 7.38/1.50  --res_forward_subs_resolution           true
% 7.38/1.50  --res_backward_subs_resolution          true
% 7.38/1.50  --res_orphan_elimination                true
% 7.38/1.50  --res_time_limit                        2.
% 7.38/1.50  --res_out_proof                         true
% 7.38/1.50  
% 7.38/1.50  ------ Superposition Options
% 7.38/1.50  
% 7.38/1.50  --superposition_flag                    true
% 7.38/1.50  --sup_passive_queue_type                priority_queues
% 7.38/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.38/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.38/1.50  --demod_completeness_check              fast
% 7.38/1.50  --demod_use_ground                      true
% 7.38/1.50  --sup_to_prop_solver                    passive
% 7.38/1.50  --sup_prop_simpl_new                    true
% 7.38/1.50  --sup_prop_simpl_given                  true
% 7.38/1.50  --sup_fun_splitting                     false
% 7.38/1.50  --sup_smt_interval                      50000
% 7.38/1.50  
% 7.38/1.50  ------ Superposition Simplification Setup
% 7.38/1.50  
% 7.38/1.50  --sup_indices_passive                   []
% 7.38/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.38/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.38/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.38/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.38/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.38/1.50  --sup_full_bw                           [BwDemod]
% 7.38/1.50  --sup_immed_triv                        [TrivRules]
% 7.38/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.38/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.38/1.50  --sup_immed_bw_main                     []
% 7.38/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.38/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.38/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.38/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.38/1.50  
% 7.38/1.50  ------ Combination Options
% 7.38/1.50  
% 7.38/1.50  --comb_res_mult                         3
% 7.38/1.50  --comb_sup_mult                         2
% 7.38/1.50  --comb_inst_mult                        10
% 7.38/1.50  
% 7.38/1.50  ------ Debug Options
% 7.38/1.50  
% 7.38/1.50  --dbg_backtrace                         false
% 7.38/1.50  --dbg_dump_prop_clauses                 false
% 7.38/1.50  --dbg_dump_prop_clauses_file            -
% 7.38/1.50  --dbg_out_stat                          false
% 7.38/1.50  ------ Parsing...
% 7.38/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.38/1.50  
% 7.38/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.38/1.50  
% 7.38/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.38/1.50  
% 7.38/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.38/1.50  ------ Proving...
% 7.38/1.50  ------ Problem Properties 
% 7.38/1.50  
% 7.38/1.50  
% 7.38/1.50  clauses                                 33
% 7.38/1.50  conjectures                             3
% 7.38/1.50  EPR                                     5
% 7.38/1.50  Horn                                    31
% 7.38/1.50  unary                                   7
% 7.38/1.50  binary                                  12
% 7.38/1.50  lits                                    74
% 7.38/1.50  lits eq                                 20
% 7.38/1.50  fd_pure                                 0
% 7.38/1.50  fd_pseudo                               0
% 7.38/1.50  fd_cond                                 1
% 7.38/1.50  fd_pseudo_cond                          1
% 7.38/1.50  AC symbols                              0
% 7.38/1.50  
% 7.38/1.50  ------ Schedule dynamic 5 is on 
% 7.38/1.50  
% 7.38/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.38/1.50  
% 7.38/1.50  
% 7.38/1.50  ------ 
% 7.38/1.50  Current options:
% 7.38/1.50  ------ 
% 7.38/1.50  
% 7.38/1.50  ------ Input Options
% 7.38/1.50  
% 7.38/1.50  --out_options                           all
% 7.38/1.50  --tptp_safe_out                         true
% 7.38/1.50  --problem_path                          ""
% 7.38/1.50  --include_path                          ""
% 7.38/1.50  --clausifier                            res/vclausify_rel
% 7.38/1.50  --clausifier_options                    --mode clausify
% 7.38/1.50  --stdin                                 false
% 7.38/1.50  --stats_out                             all
% 7.38/1.50  
% 7.38/1.50  ------ General Options
% 7.38/1.50  
% 7.38/1.50  --fof                                   false
% 7.38/1.50  --time_out_real                         305.
% 7.38/1.50  --time_out_virtual                      -1.
% 7.38/1.50  --symbol_type_check                     false
% 7.38/1.50  --clausify_out                          false
% 7.38/1.50  --sig_cnt_out                           false
% 7.38/1.50  --trig_cnt_out                          false
% 7.38/1.50  --trig_cnt_out_tolerance                1.
% 7.38/1.50  --trig_cnt_out_sk_spl                   false
% 7.38/1.50  --abstr_cl_out                          false
% 7.38/1.50  
% 7.38/1.50  ------ Global Options
% 7.38/1.50  
% 7.38/1.50  --schedule                              default
% 7.38/1.50  --add_important_lit                     false
% 7.38/1.50  --prop_solver_per_cl                    1000
% 7.38/1.50  --min_unsat_core                        false
% 7.38/1.50  --soft_assumptions                      false
% 7.38/1.50  --soft_lemma_size                       3
% 7.38/1.50  --prop_impl_unit_size                   0
% 7.38/1.50  --prop_impl_unit                        []
% 7.38/1.50  --share_sel_clauses                     true
% 7.38/1.50  --reset_solvers                         false
% 7.38/1.50  --bc_imp_inh                            [conj_cone]
% 7.38/1.50  --conj_cone_tolerance                   3.
% 7.38/1.50  --extra_neg_conj                        none
% 7.38/1.50  --large_theory_mode                     true
% 7.38/1.50  --prolific_symb_bound                   200
% 7.38/1.50  --lt_threshold                          2000
% 7.38/1.50  --clause_weak_htbl                      true
% 7.38/1.50  --gc_record_bc_elim                     false
% 7.38/1.50  
% 7.38/1.50  ------ Preprocessing Options
% 7.38/1.50  
% 7.38/1.50  --preprocessing_flag                    true
% 7.38/1.50  --time_out_prep_mult                    0.1
% 7.38/1.50  --splitting_mode                        input
% 7.38/1.50  --splitting_grd                         true
% 7.38/1.50  --splitting_cvd                         false
% 7.38/1.50  --splitting_cvd_svl                     false
% 7.38/1.50  --splitting_nvd                         32
% 7.38/1.50  --sub_typing                            true
% 7.38/1.50  --prep_gs_sim                           true
% 7.38/1.50  --prep_unflatten                        true
% 7.38/1.50  --prep_res_sim                          true
% 7.38/1.50  --prep_upred                            true
% 7.38/1.50  --prep_sem_filter                       exhaustive
% 7.38/1.50  --prep_sem_filter_out                   false
% 7.38/1.50  --pred_elim                             true
% 7.38/1.50  --res_sim_input                         true
% 7.38/1.50  --eq_ax_congr_red                       true
% 7.38/1.50  --pure_diseq_elim                       true
% 7.38/1.50  --brand_transform                       false
% 7.38/1.50  --non_eq_to_eq                          false
% 7.38/1.50  --prep_def_merge                        true
% 7.38/1.50  --prep_def_merge_prop_impl              false
% 7.38/1.50  --prep_def_merge_mbd                    true
% 7.38/1.50  --prep_def_merge_tr_red                 false
% 7.38/1.50  --prep_def_merge_tr_cl                  false
% 7.38/1.50  --smt_preprocessing                     true
% 7.38/1.50  --smt_ac_axioms                         fast
% 7.38/1.50  --preprocessed_out                      false
% 7.38/1.50  --preprocessed_stats                    false
% 7.38/1.50  
% 7.38/1.50  ------ Abstraction refinement Options
% 7.38/1.50  
% 7.38/1.50  --abstr_ref                             []
% 7.38/1.50  --abstr_ref_prep                        false
% 7.38/1.50  --abstr_ref_until_sat                   false
% 7.38/1.50  --abstr_ref_sig_restrict                funpre
% 7.38/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.38/1.50  --abstr_ref_under                       []
% 7.38/1.50  
% 7.38/1.50  ------ SAT Options
% 7.38/1.50  
% 7.38/1.50  --sat_mode                              false
% 7.38/1.50  --sat_fm_restart_options                ""
% 7.38/1.50  --sat_gr_def                            false
% 7.38/1.50  --sat_epr_types                         true
% 7.38/1.50  --sat_non_cyclic_types                  false
% 7.38/1.50  --sat_finite_models                     false
% 7.38/1.50  --sat_fm_lemmas                         false
% 7.38/1.50  --sat_fm_prep                           false
% 7.38/1.50  --sat_fm_uc_incr                        true
% 7.38/1.50  --sat_out_model                         small
% 7.38/1.50  --sat_out_clauses                       false
% 7.38/1.50  
% 7.38/1.50  ------ QBF Options
% 7.38/1.50  
% 7.38/1.50  --qbf_mode                              false
% 7.38/1.50  --qbf_elim_univ                         false
% 7.38/1.50  --qbf_dom_inst                          none
% 7.38/1.50  --qbf_dom_pre_inst                      false
% 7.38/1.50  --qbf_sk_in                             false
% 7.38/1.50  --qbf_pred_elim                         true
% 7.38/1.50  --qbf_split                             512
% 7.38/1.50  
% 7.38/1.50  ------ BMC1 Options
% 7.38/1.50  
% 7.38/1.50  --bmc1_incremental                      false
% 7.38/1.50  --bmc1_axioms                           reachable_all
% 7.38/1.50  --bmc1_min_bound                        0
% 7.38/1.50  --bmc1_max_bound                        -1
% 7.38/1.50  --bmc1_max_bound_default                -1
% 7.38/1.50  --bmc1_symbol_reachability              true
% 7.38/1.50  --bmc1_property_lemmas                  false
% 7.38/1.50  --bmc1_k_induction                      false
% 7.38/1.50  --bmc1_non_equiv_states                 false
% 7.38/1.50  --bmc1_deadlock                         false
% 7.38/1.50  --bmc1_ucm                              false
% 7.38/1.50  --bmc1_add_unsat_core                   none
% 7.38/1.50  --bmc1_unsat_core_children              false
% 7.38/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.38/1.50  --bmc1_out_stat                         full
% 7.38/1.50  --bmc1_ground_init                      false
% 7.38/1.50  --bmc1_pre_inst_next_state              false
% 7.38/1.50  --bmc1_pre_inst_state                   false
% 7.38/1.50  --bmc1_pre_inst_reach_state             false
% 7.38/1.50  --bmc1_out_unsat_core                   false
% 7.38/1.50  --bmc1_aig_witness_out                  false
% 7.38/1.50  --bmc1_verbose                          false
% 7.38/1.50  --bmc1_dump_clauses_tptp                false
% 7.38/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.38/1.50  --bmc1_dump_file                        -
% 7.38/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.38/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.38/1.50  --bmc1_ucm_extend_mode                  1
% 7.38/1.50  --bmc1_ucm_init_mode                    2
% 7.38/1.50  --bmc1_ucm_cone_mode                    none
% 7.38/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.38/1.50  --bmc1_ucm_relax_model                  4
% 7.38/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.38/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.38/1.50  --bmc1_ucm_layered_model                none
% 7.38/1.50  --bmc1_ucm_max_lemma_size               10
% 7.38/1.50  
% 7.38/1.50  ------ AIG Options
% 7.38/1.50  
% 7.38/1.50  --aig_mode                              false
% 7.38/1.50  
% 7.38/1.50  ------ Instantiation Options
% 7.38/1.50  
% 7.38/1.50  --instantiation_flag                    true
% 7.38/1.50  --inst_sos_flag                         false
% 7.38/1.50  --inst_sos_phase                        true
% 7.38/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.38/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.38/1.50  --inst_lit_sel_side                     none
% 7.38/1.50  --inst_solver_per_active                1400
% 7.38/1.50  --inst_solver_calls_frac                1.
% 7.38/1.50  --inst_passive_queue_type               priority_queues
% 7.38/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.38/1.50  --inst_passive_queues_freq              [25;2]
% 7.38/1.50  --inst_dismatching                      true
% 7.38/1.50  --inst_eager_unprocessed_to_passive     true
% 7.38/1.50  --inst_prop_sim_given                   true
% 7.38/1.50  --inst_prop_sim_new                     false
% 7.38/1.50  --inst_subs_new                         false
% 7.38/1.50  --inst_eq_res_simp                      false
% 7.38/1.50  --inst_subs_given                       false
% 7.38/1.50  --inst_orphan_elimination               true
% 7.38/1.50  --inst_learning_loop_flag               true
% 7.38/1.50  --inst_learning_start                   3000
% 7.38/1.50  --inst_learning_factor                  2
% 7.38/1.50  --inst_start_prop_sim_after_learn       3
% 7.38/1.50  --inst_sel_renew                        solver
% 7.38/1.50  --inst_lit_activity_flag                true
% 7.38/1.50  --inst_restr_to_given                   false
% 7.38/1.50  --inst_activity_threshold               500
% 7.38/1.50  --inst_out_proof                        true
% 7.38/1.50  
% 7.38/1.50  ------ Resolution Options
% 7.38/1.50  
% 7.38/1.50  --resolution_flag                       false
% 7.38/1.50  --res_lit_sel                           adaptive
% 7.38/1.50  --res_lit_sel_side                      none
% 7.38/1.50  --res_ordering                          kbo
% 7.38/1.50  --res_to_prop_solver                    active
% 7.38/1.50  --res_prop_simpl_new                    false
% 7.38/1.50  --res_prop_simpl_given                  true
% 7.38/1.50  --res_passive_queue_type                priority_queues
% 7.38/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.38/1.50  --res_passive_queues_freq               [15;5]
% 7.38/1.50  --res_forward_subs                      full
% 7.38/1.50  --res_backward_subs                     full
% 7.38/1.50  --res_forward_subs_resolution           true
% 7.38/1.50  --res_backward_subs_resolution          true
% 7.38/1.50  --res_orphan_elimination                true
% 7.38/1.50  --res_time_limit                        2.
% 7.38/1.50  --res_out_proof                         true
% 7.38/1.50  
% 7.38/1.50  ------ Superposition Options
% 7.38/1.50  
% 7.38/1.50  --superposition_flag                    true
% 7.38/1.50  --sup_passive_queue_type                priority_queues
% 7.38/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.38/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.38/1.50  --demod_completeness_check              fast
% 7.38/1.50  --demod_use_ground                      true
% 7.38/1.50  --sup_to_prop_solver                    passive
% 7.38/1.50  --sup_prop_simpl_new                    true
% 7.38/1.50  --sup_prop_simpl_given                  true
% 7.38/1.50  --sup_fun_splitting                     false
% 7.38/1.50  --sup_smt_interval                      50000
% 7.38/1.50  
% 7.38/1.50  ------ Superposition Simplification Setup
% 7.38/1.50  
% 7.38/1.50  --sup_indices_passive                   []
% 7.38/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.38/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.38/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.38/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.38/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.38/1.50  --sup_full_bw                           [BwDemod]
% 7.38/1.50  --sup_immed_triv                        [TrivRules]
% 7.38/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.38/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.38/1.50  --sup_immed_bw_main                     []
% 7.38/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.38/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.38/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.38/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.38/1.50  
% 7.38/1.50  ------ Combination Options
% 7.38/1.50  
% 7.38/1.50  --comb_res_mult                         3
% 7.38/1.50  --comb_sup_mult                         2
% 7.38/1.50  --comb_inst_mult                        10
% 7.38/1.50  
% 7.38/1.50  ------ Debug Options
% 7.38/1.50  
% 7.38/1.50  --dbg_backtrace                         false
% 7.38/1.50  --dbg_dump_prop_clauses                 false
% 7.38/1.50  --dbg_dump_prop_clauses_file            -
% 7.38/1.50  --dbg_out_stat                          false
% 7.38/1.50  
% 7.38/1.50  
% 7.38/1.50  
% 7.38/1.50  
% 7.38/1.50  ------ Proving...
% 7.38/1.50  
% 7.38/1.50  
% 7.38/1.50  % SZS status Theorem for theBenchmark.p
% 7.38/1.50  
% 7.38/1.50   Resolution empty clause
% 7.38/1.50  
% 7.38/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.38/1.50  
% 7.38/1.50  fof(f10,axiom,(
% 7.38/1.50    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.38/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.50  
% 7.38/1.50  fof(f58,plain,(
% 7.38/1.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.38/1.50    inference(nnf_transformation,[],[f10])).
% 7.38/1.50  
% 7.38/1.50  fof(f59,plain,(
% 7.38/1.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.38/1.50    inference(flattening,[],[f58])).
% 7.38/1.50  
% 7.38/1.50  fof(f81,plain,(
% 7.38/1.50    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 7.38/1.50    inference(cnf_transformation,[],[f59])).
% 7.38/1.50  
% 7.38/1.50  fof(f125,plain,(
% 7.38/1.50    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 7.38/1.50    inference(equality_resolution,[],[f81])).
% 7.38/1.50  
% 7.38/1.50  fof(f16,axiom,(
% 7.38/1.50    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 7.38/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.50  
% 7.38/1.50  fof(f36,plain,(
% 7.38/1.50    ! [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 7.38/1.50    inference(ennf_transformation,[],[f16])).
% 7.38/1.50  
% 7.38/1.50  fof(f64,plain,(
% 7.38/1.50    ! [X0,X1] : (((r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0)) & (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)))) | ~v1_relat_1(X1))),
% 7.38/1.50    inference(nnf_transformation,[],[f36])).
% 7.38/1.50  
% 7.38/1.50  fof(f92,plain,(
% 7.38/1.50    ( ! [X0,X1] : (r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.38/1.50    inference(cnf_transformation,[],[f64])).
% 7.38/1.50  
% 7.38/1.50  fof(f11,axiom,(
% 7.38/1.50    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 7.38/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.50  
% 7.38/1.50  fof(f60,plain,(
% 7.38/1.50    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 7.38/1.50    inference(nnf_transformation,[],[f11])).
% 7.38/1.50  
% 7.38/1.50  fof(f61,plain,(
% 7.38/1.50    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 7.38/1.50    inference(flattening,[],[f60])).
% 7.38/1.50  
% 7.38/1.50  fof(f84,plain,(
% 7.38/1.50    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 7.38/1.50    inference(cnf_transformation,[],[f61])).
% 7.38/1.50  
% 7.38/1.50  fof(f4,axiom,(
% 7.38/1.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.38/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.50  
% 7.38/1.50  fof(f73,plain,(
% 7.38/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.38/1.50    inference(cnf_transformation,[],[f4])).
% 7.38/1.50  
% 7.38/1.50  fof(f5,axiom,(
% 7.38/1.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.38/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.50  
% 7.38/1.50  fof(f74,plain,(
% 7.38/1.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.38/1.50    inference(cnf_transformation,[],[f5])).
% 7.38/1.50  
% 7.38/1.50  fof(f6,axiom,(
% 7.38/1.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.38/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.50  
% 7.38/1.50  fof(f75,plain,(
% 7.38/1.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.38/1.50    inference(cnf_transformation,[],[f6])).
% 7.38/1.50  
% 7.38/1.50  fof(f7,axiom,(
% 7.38/1.50    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.38/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.50  
% 7.38/1.50  fof(f76,plain,(
% 7.38/1.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.38/1.50    inference(cnf_transformation,[],[f7])).
% 7.38/1.50  
% 7.38/1.50  fof(f8,axiom,(
% 7.38/1.50    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 7.38/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.50  
% 7.38/1.50  fof(f77,plain,(
% 7.38/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 7.38/1.50    inference(cnf_transformation,[],[f8])).
% 7.38/1.50  
% 7.38/1.50  fof(f9,axiom,(
% 7.38/1.50    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 7.38/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.50  
% 7.38/1.50  fof(f78,plain,(
% 7.38/1.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 7.38/1.50    inference(cnf_transformation,[],[f9])).
% 7.38/1.50  
% 7.38/1.50  fof(f110,plain,(
% 7.38/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 7.38/1.50    inference(definition_unfolding,[],[f77,f78])).
% 7.38/1.50  
% 7.38/1.50  fof(f111,plain,(
% 7.38/1.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 7.38/1.50    inference(definition_unfolding,[],[f76,f110])).
% 7.38/1.50  
% 7.38/1.50  fof(f112,plain,(
% 7.38/1.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 7.38/1.50    inference(definition_unfolding,[],[f75,f111])).
% 7.38/1.50  
% 7.38/1.50  fof(f113,plain,(
% 7.38/1.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 7.38/1.50    inference(definition_unfolding,[],[f74,f112])).
% 7.38/1.50  
% 7.38/1.50  fof(f114,plain,(
% 7.38/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 7.38/1.50    inference(definition_unfolding,[],[f73,f113])).
% 7.38/1.50  
% 7.38/1.50  fof(f116,plain,(
% 7.38/1.50    ( ! [X2,X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 7.38/1.50    inference(definition_unfolding,[],[f84,f114])).
% 7.38/1.50  
% 7.38/1.50  fof(f29,conjecture,(
% 7.38/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 7.38/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.50  
% 7.38/1.50  fof(f30,negated_conjecture,(
% 7.38/1.50    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 7.38/1.50    inference(negated_conjecture,[],[f29])).
% 7.38/1.50  
% 7.38/1.50  fof(f31,plain,(
% 7.38/1.50    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 7.38/1.50    inference(pure_predicate_removal,[],[f30])).
% 7.38/1.50  
% 7.38/1.50  fof(f54,plain,(
% 7.38/1.50    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 7.38/1.50    inference(ennf_transformation,[],[f31])).
% 7.38/1.50  
% 7.38/1.50  fof(f55,plain,(
% 7.38/1.50    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 7.38/1.50    inference(flattening,[],[f54])).
% 7.38/1.50  
% 7.38/1.50  fof(f66,plain,(
% 7.38/1.50    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3))),
% 7.38/1.50    introduced(choice_axiom,[])).
% 7.38/1.50  
% 7.38/1.50  fof(f67,plain,(
% 7.38/1.50    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3)),
% 7.38/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f55,f66])).
% 7.38/1.50  
% 7.38/1.50  fof(f107,plain,(
% 7.38/1.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 7.38/1.50    inference(cnf_transformation,[],[f67])).
% 7.38/1.50  
% 7.38/1.50  fof(f3,axiom,(
% 7.38/1.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.38/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.50  
% 7.38/1.50  fof(f72,plain,(
% 7.38/1.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.38/1.50    inference(cnf_transformation,[],[f3])).
% 7.38/1.50  
% 7.38/1.50  fof(f115,plain,(
% 7.38/1.50    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 7.38/1.50    inference(definition_unfolding,[],[f72,f114])).
% 7.38/1.50  
% 7.38/1.50  fof(f122,plain,(
% 7.38/1.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))),
% 7.38/1.50    inference(definition_unfolding,[],[f107,f115])).
% 7.38/1.50  
% 7.38/1.50  fof(f25,axiom,(
% 7.38/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.38/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.50  
% 7.38/1.50  fof(f48,plain,(
% 7.38/1.50    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.38/1.50    inference(ennf_transformation,[],[f25])).
% 7.38/1.50  
% 7.38/1.50  fof(f102,plain,(
% 7.38/1.50    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.38/1.50    inference(cnf_transformation,[],[f48])).
% 7.38/1.50  
% 7.38/1.50  fof(f23,axiom,(
% 7.38/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 7.38/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.50  
% 7.38/1.50  fof(f46,plain,(
% 7.38/1.50    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.38/1.50    inference(ennf_transformation,[],[f23])).
% 7.38/1.50  
% 7.38/1.50  fof(f100,plain,(
% 7.38/1.50    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.38/1.50    inference(cnf_transformation,[],[f46])).
% 7.38/1.50  
% 7.38/1.50  fof(f21,axiom,(
% 7.38/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.38/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.50  
% 7.38/1.50  fof(f44,plain,(
% 7.38/1.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.38/1.50    inference(ennf_transformation,[],[f21])).
% 7.38/1.50  
% 7.38/1.50  fof(f98,plain,(
% 7.38/1.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.38/1.50    inference(cnf_transformation,[],[f44])).
% 7.38/1.50  
% 7.38/1.50  fof(f22,axiom,(
% 7.38/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.38/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.50  
% 7.38/1.50  fof(f32,plain,(
% 7.38/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.38/1.50    inference(pure_predicate_removal,[],[f22])).
% 7.38/1.50  
% 7.38/1.50  fof(f45,plain,(
% 7.38/1.50    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.38/1.50    inference(ennf_transformation,[],[f32])).
% 7.38/1.50  
% 7.38/1.50  fof(f99,plain,(
% 7.38/1.50    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.38/1.50    inference(cnf_transformation,[],[f45])).
% 7.38/1.50  
% 7.38/1.50  fof(f14,axiom,(
% 7.38/1.50    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 7.38/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.50  
% 7.38/1.50  fof(f34,plain,(
% 7.38/1.50    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.38/1.50    inference(ennf_transformation,[],[f14])).
% 7.38/1.50  
% 7.38/1.50  fof(f63,plain,(
% 7.38/1.50    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.38/1.50    inference(nnf_transformation,[],[f34])).
% 7.38/1.50  
% 7.38/1.50  fof(f88,plain,(
% 7.38/1.50    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.38/1.50    inference(cnf_transformation,[],[f63])).
% 7.38/1.50  
% 7.38/1.50  fof(f12,axiom,(
% 7.38/1.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.38/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.50  
% 7.38/1.50  fof(f62,plain,(
% 7.38/1.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.38/1.50    inference(nnf_transformation,[],[f12])).
% 7.38/1.50  
% 7.38/1.50  fof(f86,plain,(
% 7.38/1.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.38/1.50    inference(cnf_transformation,[],[f62])).
% 7.38/1.50  
% 7.38/1.50  fof(f85,plain,(
% 7.38/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.38/1.50    inference(cnf_transformation,[],[f62])).
% 7.38/1.50  
% 7.38/1.50  fof(f1,axiom,(
% 7.38/1.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.38/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.50  
% 7.38/1.50  fof(f56,plain,(
% 7.38/1.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.38/1.50    inference(nnf_transformation,[],[f1])).
% 7.38/1.50  
% 7.38/1.50  fof(f57,plain,(
% 7.38/1.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.38/1.50    inference(flattening,[],[f56])).
% 7.38/1.50  
% 7.38/1.50  fof(f70,plain,(
% 7.38/1.50    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.38/1.50    inference(cnf_transformation,[],[f57])).
% 7.38/1.50  
% 7.38/1.50  fof(f13,axiom,(
% 7.38/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 7.38/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.50  
% 7.38/1.50  fof(f33,plain,(
% 7.38/1.50    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 7.38/1.50    inference(ennf_transformation,[],[f13])).
% 7.38/1.50  
% 7.38/1.50  fof(f87,plain,(
% 7.38/1.50    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 7.38/1.50    inference(cnf_transformation,[],[f33])).
% 7.38/1.50  
% 7.38/1.50  fof(f119,plain,(
% 7.38/1.50    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 7.38/1.50    inference(definition_unfolding,[],[f87,f115])).
% 7.38/1.50  
% 7.38/1.50  fof(f17,axiom,(
% 7.38/1.50    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 7.38/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.50  
% 7.38/1.50  fof(f37,plain,(
% 7.38/1.50    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.38/1.50    inference(ennf_transformation,[],[f17])).
% 7.38/1.50  
% 7.38/1.50  fof(f38,plain,(
% 7.38/1.50    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.38/1.50    inference(flattening,[],[f37])).
% 7.38/1.50  
% 7.38/1.50  fof(f93,plain,(
% 7.38/1.50    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.38/1.50    inference(cnf_transformation,[],[f38])).
% 7.38/1.50  
% 7.38/1.50  fof(f15,axiom,(
% 7.38/1.50    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 7.38/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.50  
% 7.38/1.50  fof(f35,plain,(
% 7.38/1.50    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 7.38/1.50    inference(ennf_transformation,[],[f15])).
% 7.38/1.50  
% 7.38/1.50  fof(f90,plain,(
% 7.38/1.50    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 7.38/1.50    inference(cnf_transformation,[],[f35])).
% 7.38/1.50  
% 7.38/1.50  fof(f20,axiom,(
% 7.38/1.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 7.38/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.50  
% 7.38/1.50  fof(f42,plain,(
% 7.38/1.50    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.38/1.50    inference(ennf_transformation,[],[f20])).
% 7.38/1.50  
% 7.38/1.50  fof(f43,plain,(
% 7.38/1.50    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.38/1.50    inference(flattening,[],[f42])).
% 7.38/1.50  
% 7.38/1.50  fof(f97,plain,(
% 7.38/1.50    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.38/1.50    inference(cnf_transformation,[],[f43])).
% 7.38/1.50  
% 7.38/1.50  fof(f120,plain,(
% 7.38/1.50    ( ! [X0,X1] : (k6_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.38/1.50    inference(definition_unfolding,[],[f97,f115,f115])).
% 7.38/1.50  
% 7.38/1.50  fof(f106,plain,(
% 7.38/1.50    v1_funct_1(sK3)),
% 7.38/1.50    inference(cnf_transformation,[],[f67])).
% 7.38/1.50  
% 7.38/1.50  fof(f26,axiom,(
% 7.38/1.50    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 7.38/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.50  
% 7.38/1.50  fof(f49,plain,(
% 7.38/1.50    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.38/1.50    inference(ennf_transformation,[],[f26])).
% 7.38/1.50  
% 7.38/1.50  fof(f103,plain,(
% 7.38/1.50    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.38/1.50    inference(cnf_transformation,[],[f49])).
% 7.38/1.50  
% 7.38/1.50  fof(f109,plain,(
% 7.38/1.50    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 7.38/1.50    inference(cnf_transformation,[],[f67])).
% 7.38/1.50  
% 7.38/1.50  fof(f121,plain,(
% 7.38/1.50    ~r1_tarski(k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 7.38/1.50    inference(definition_unfolding,[],[f109,f115,f115])).
% 7.38/1.50  
% 7.38/1.50  fof(f69,plain,(
% 7.38/1.50    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 7.38/1.50    inference(cnf_transformation,[],[f57])).
% 7.38/1.50  
% 7.38/1.50  fof(f123,plain,(
% 7.38/1.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.38/1.50    inference(equality_resolution,[],[f69])).
% 7.38/1.50  
% 7.38/1.50  fof(f28,axiom,(
% 7.38/1.50    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_tarski(k2_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))),
% 7.38/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.50  
% 7.38/1.50  fof(f52,plain,(
% 7.38/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 7.38/1.50    inference(ennf_transformation,[],[f28])).
% 7.38/1.50  
% 7.38/1.50  fof(f53,plain,(
% 7.38/1.50    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 7.38/1.50    inference(flattening,[],[f52])).
% 7.38/1.50  
% 7.38/1.50  fof(f105,plain,(
% 7.38/1.50    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) )),
% 7.38/1.50    inference(cnf_transformation,[],[f53])).
% 7.38/1.50  
% 7.38/1.50  fof(f24,axiom,(
% 7.38/1.50    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 7.38/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.50  
% 7.38/1.50  fof(f47,plain,(
% 7.38/1.50    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.38/1.50    inference(ennf_transformation,[],[f24])).
% 7.38/1.50  
% 7.38/1.50  fof(f101,plain,(
% 7.38/1.50    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.38/1.50    inference(cnf_transformation,[],[f47])).
% 7.38/1.50  
% 7.38/1.50  fof(f2,axiom,(
% 7.38/1.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.38/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.50  
% 7.38/1.50  fof(f71,plain,(
% 7.38/1.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.38/1.50    inference(cnf_transformation,[],[f2])).
% 7.38/1.50  
% 7.38/1.50  fof(f80,plain,(
% 7.38/1.50    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 7.38/1.50    inference(cnf_transformation,[],[f59])).
% 7.38/1.50  
% 7.38/1.50  fof(f126,plain,(
% 7.38/1.50    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 7.38/1.50    inference(equality_resolution,[],[f80])).
% 7.38/1.50  
% 7.38/1.50  fof(f27,axiom,(
% 7.38/1.50    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 7.38/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.50  
% 7.38/1.50  fof(f50,plain,(
% 7.38/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 7.38/1.50    inference(ennf_transformation,[],[f27])).
% 7.38/1.50  
% 7.38/1.50  fof(f51,plain,(
% 7.38/1.50    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 7.38/1.50    inference(flattening,[],[f50])).
% 7.38/1.50  
% 7.38/1.50  fof(f104,plain,(
% 7.38/1.50    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 7.38/1.50    inference(cnf_transformation,[],[f51])).
% 7.38/1.50  
% 7.38/1.50  cnf(c_4,plain,
% 7.38/1.50      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.38/1.50      inference(cnf_transformation,[],[f125]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_16,plain,
% 7.38/1.50      ( r2_hidden(X0,k1_relat_1(X1))
% 7.38/1.50      | ~ v1_relat_1(X1)
% 7.38/1.50      | k11_relat_1(X1,X0) = k1_xboole_0 ),
% 7.38/1.50      inference(cnf_transformation,[],[f92]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_1745,plain,
% 7.38/1.50      ( k11_relat_1(X0,X1) = k1_xboole_0
% 7.38/1.50      | r2_hidden(X1,k1_relat_1(X0)) = iProver_top
% 7.38/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.38/1.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_7,plain,
% 7.38/1.50      ( ~ r2_hidden(X0,X1)
% 7.38/1.50      | ~ r2_hidden(X2,X1)
% 7.38/1.50      | r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0),X1) ),
% 7.38/1.50      inference(cnf_transformation,[],[f116]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_1754,plain,
% 7.38/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.38/1.50      | r2_hidden(X2,X1) != iProver_top
% 7.38/1.50      | r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0),X1) = iProver_top ),
% 7.38/1.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_33,negated_conjecture,
% 7.38/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) ),
% 7.38/1.50      inference(cnf_transformation,[],[f122]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_1730,plain,
% 7.38/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
% 7.38/1.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_27,plain,
% 7.38/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.38/1.50      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.38/1.50      inference(cnf_transformation,[],[f102]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_1735,plain,
% 7.38/1.50      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.38/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.38/1.50      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_3643,plain,
% 7.38/1.50      ( k1_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3) = k1_relat_1(sK3) ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_1730,c_1735]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_25,plain,
% 7.38/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.38/1.50      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 7.38/1.50      inference(cnf_transformation,[],[f100]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_1737,plain,
% 7.38/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.38/1.50      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 7.38/1.50      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_4314,plain,
% 7.38/1.50      ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = iProver_top
% 7.38/1.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) != iProver_top ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_3643,c_1737]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_36,plain,
% 7.38/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
% 7.38/1.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_23,plain,
% 7.38/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 7.38/1.50      inference(cnf_transformation,[],[f98]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_1983,plain,
% 7.38/1.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))
% 7.38/1.50      | v1_relat_1(sK3) ),
% 7.38/1.50      inference(instantiation,[status(thm)],[c_23]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_1984,plain,
% 7.38/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) != iProver_top
% 7.38/1.50      | v1_relat_1(sK3) = iProver_top ),
% 7.38/1.50      inference(predicate_to_equality,[status(thm)],[c_1983]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_24,plain,
% 7.38/1.50      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.38/1.50      inference(cnf_transformation,[],[f99]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_1995,plain,
% 7.38/1.50      ( v4_relat_1(sK3,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
% 7.38/1.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) ),
% 7.38/1.50      inference(instantiation,[status(thm)],[c_24]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_1996,plain,
% 7.38/1.50      ( v4_relat_1(sK3,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top
% 7.38/1.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) != iProver_top ),
% 7.38/1.50      inference(predicate_to_equality,[status(thm)],[c_1995]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_14,plain,
% 7.38/1.50      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 7.38/1.50      inference(cnf_transformation,[],[f88]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_2117,plain,
% 7.38/1.50      ( ~ v4_relat_1(sK3,X0)
% 7.38/1.50      | r1_tarski(k1_relat_1(sK3),X0)
% 7.38/1.50      | ~ v1_relat_1(sK3) ),
% 7.38/1.50      inference(instantiation,[status(thm)],[c_14]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_2311,plain,
% 7.38/1.50      ( ~ v4_relat_1(sK3,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
% 7.38/1.50      | r1_tarski(k1_relat_1(sK3),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
% 7.38/1.50      | ~ v1_relat_1(sK3) ),
% 7.38/1.50      inference(instantiation,[status(thm)],[c_2117]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_2312,plain,
% 7.38/1.50      ( v4_relat_1(sK3,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != iProver_top
% 7.38/1.50      | r1_tarski(k1_relat_1(sK3),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top
% 7.38/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.38/1.50      inference(predicate_to_equality,[status(thm)],[c_2311]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_10,plain,
% 7.38/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.38/1.50      inference(cnf_transformation,[],[f86]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_2440,plain,
% 7.38/1.50      ( m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(X1))
% 7.38/1.50      | ~ r1_tarski(k1_relat_1(X0),X1) ),
% 7.38/1.50      inference(instantiation,[status(thm)],[c_10]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_3364,plain,
% 7.38/1.50      ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
% 7.38/1.50      | ~ r1_tarski(k1_relat_1(sK3),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
% 7.38/1.50      inference(instantiation,[status(thm)],[c_2440]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_3365,plain,
% 7.38/1.50      ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = iProver_top
% 7.38/1.50      | r1_tarski(k1_relat_1(sK3),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != iProver_top ),
% 7.38/1.50      inference(predicate_to_equality,[status(thm)],[c_3364]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_4637,plain,
% 7.38/1.50      ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = iProver_top ),
% 7.38/1.50      inference(global_propositional_subsumption,
% 7.38/1.50                [status(thm)],
% 7.38/1.50                [c_4314,c_36,c_1984,c_1996,c_2312,c_3365]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_11,plain,
% 7.38/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.38/1.50      inference(cnf_transformation,[],[f85]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_1750,plain,
% 7.38/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.38/1.50      | r1_tarski(X0,X1) = iProver_top ),
% 7.38/1.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_4642,plain,
% 7.38/1.50      ( r1_tarski(k1_relat_1(sK3),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_4637,c_1750]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_0,plain,
% 7.38/1.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.38/1.50      inference(cnf_transformation,[],[f70]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_1757,plain,
% 7.38/1.50      ( X0 = X1
% 7.38/1.50      | r1_tarski(X0,X1) != iProver_top
% 7.38/1.50      | r1_tarski(X1,X0) != iProver_top ),
% 7.38/1.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_4972,plain,
% 7.38/1.50      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
% 7.38/1.50      | r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_relat_1(sK3)) != iProver_top ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_4642,c_1757]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_11932,plain,
% 7.38/1.50      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
% 7.38/1.50      | r2_hidden(sK0,k1_relat_1(sK3)) != iProver_top ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_1754,c_4972]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_17228,plain,
% 7.38/1.50      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
% 7.38/1.50      | k11_relat_1(sK3,sK0) = k1_xboole_0
% 7.38/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_1745,c_11932]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_1739,plain,
% 7.38/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.38/1.50      | v1_relat_1(X0) = iProver_top ),
% 7.38/1.50      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_2545,plain,
% 7.38/1.50      ( v1_relat_1(sK3) = iProver_top ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_1730,c_1739]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_12,plain,
% 7.38/1.50      ( ~ v1_relat_1(X0)
% 7.38/1.50      | k9_relat_1(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
% 7.38/1.50      inference(cnf_transformation,[],[f119]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_1749,plain,
% 7.38/1.50      ( k9_relat_1(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k11_relat_1(X0,X1)
% 7.38/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.38/1.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_8447,plain,
% 7.38/1.50      ( k9_relat_1(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k11_relat_1(sK3,X0) ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_2545,c_1749]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_1738,plain,
% 7.38/1.50      ( v4_relat_1(X0,X1) = iProver_top
% 7.38/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 7.38/1.50      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_2831,plain,
% 7.38/1.50      ( v4_relat_1(sK3,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_1730,c_1738]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_18,plain,
% 7.38/1.50      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 7.38/1.50      inference(cnf_transformation,[],[f93]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_1743,plain,
% 7.38/1.50      ( k7_relat_1(X0,X1) = X0
% 7.38/1.50      | v4_relat_1(X0,X1) != iProver_top
% 7.38/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.38/1.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_5144,plain,
% 7.38/1.50      ( k7_relat_1(sK3,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = sK3
% 7.38/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_2831,c_1743]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_2114,plain,
% 7.38/1.50      ( ~ v4_relat_1(sK3,X0) | ~ v1_relat_1(sK3) | k7_relat_1(sK3,X0) = sK3 ),
% 7.38/1.50      inference(instantiation,[status(thm)],[c_18]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_2300,plain,
% 7.38/1.50      ( ~ v4_relat_1(sK3,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
% 7.38/1.50      | ~ v1_relat_1(sK3)
% 7.38/1.50      | k7_relat_1(sK3,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = sK3 ),
% 7.38/1.50      inference(instantiation,[status(thm)],[c_2114]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_5253,plain,
% 7.38/1.50      ( k7_relat_1(sK3,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = sK3 ),
% 7.38/1.50      inference(global_propositional_subsumption,
% 7.38/1.50                [status(thm)],
% 7.38/1.50                [c_5144,c_33,c_1983,c_1995,c_2300]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_15,plain,
% 7.38/1.50      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 7.38/1.50      inference(cnf_transformation,[],[f90]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_1746,plain,
% 7.38/1.50      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 7.38/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.38/1.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_2795,plain,
% 7.38/1.50      ( k2_relat_1(k7_relat_1(sK3,X0)) = k9_relat_1(sK3,X0) ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_2545,c_1746]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_5256,plain,
% 7.38/1.50      ( k9_relat_1(sK3,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k2_relat_1(sK3) ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_5253,c_2795]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_8973,plain,
% 7.38/1.50      ( k11_relat_1(sK3,sK0) = k2_relat_1(sK3) ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_8447,c_5256]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_17229,plain,
% 7.38/1.50      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
% 7.38/1.50      | k2_relat_1(sK3) = k1_xboole_0
% 7.38/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.38/1.50      inference(demodulation,[status(thm)],[c_17228,c_8973]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_17230,plain,
% 7.38/1.50      ( ~ v1_relat_1(sK3)
% 7.38/1.50      | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
% 7.38/1.50      | k2_relat_1(sK3) = k1_xboole_0 ),
% 7.38/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_17229]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_17398,plain,
% 7.38/1.50      ( k2_relat_1(sK3) = k1_xboole_0
% 7.38/1.50      | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(sK3) ),
% 7.38/1.50      inference(global_propositional_subsumption,
% 7.38/1.50                [status(thm)],
% 7.38/1.50                [c_17229,c_33,c_1983,c_17230]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_17399,plain,
% 7.38/1.50      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
% 7.38/1.50      | k2_relat_1(sK3) = k1_xboole_0 ),
% 7.38/1.50      inference(renaming,[status(thm)],[c_17398]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_22,plain,
% 7.38/1.50      ( ~ v1_funct_1(X0)
% 7.38/1.50      | ~ v1_relat_1(X0)
% 7.38/1.50      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k1_relat_1(X0)
% 7.38/1.50      | k6_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
% 7.38/1.50      inference(cnf_transformation,[],[f120]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_34,negated_conjecture,
% 7.38/1.50      ( v1_funct_1(sK3) ),
% 7.38/1.50      inference(cnf_transformation,[],[f106]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_415,plain,
% 7.38/1.50      ( ~ v1_relat_1(X0)
% 7.38/1.50      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k1_relat_1(X0)
% 7.38/1.50      | k6_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
% 7.38/1.50      | sK3 != X0 ),
% 7.38/1.50      inference(resolution_lifted,[status(thm)],[c_22,c_34]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_416,plain,
% 7.38/1.50      ( ~ v1_relat_1(sK3)
% 7.38/1.50      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(sK3)
% 7.38/1.50      | k6_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
% 7.38/1.50      inference(unflattening,[status(thm)],[c_415]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_1729,plain,
% 7.38/1.50      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(sK3)
% 7.38/1.50      | k6_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
% 7.38/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.38/1.50      inference(predicate_to_equality,[status(thm)],[c_416]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_417,plain,
% 7.38/1.50      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(sK3)
% 7.38/1.50      | k6_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
% 7.38/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.38/1.50      inference(predicate_to_equality,[status(thm)],[c_416]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_1989,plain,
% 7.38/1.50      ( k6_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
% 7.38/1.50      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(sK3) ),
% 7.38/1.50      inference(global_propositional_subsumption,
% 7.38/1.50                [status(thm)],
% 7.38/1.50                [c_1729,c_36,c_417,c_1984]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_1990,plain,
% 7.38/1.50      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(sK3)
% 7.38/1.50      | k6_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
% 7.38/1.50      inference(renaming,[status(thm)],[c_1989]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_17406,plain,
% 7.38/1.50      ( k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
% 7.38/1.50      | k2_relat_1(sK3) = k1_xboole_0 ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_17399,c_1990]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_28,plain,
% 7.38/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.38/1.50      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 7.38/1.50      inference(cnf_transformation,[],[f103]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_1734,plain,
% 7.38/1.50      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 7.38/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.38/1.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_6289,plain,
% 7.38/1.50      ( k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_1730,c_1734]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_31,negated_conjecture,
% 7.38/1.50      ( ~ r1_tarski(k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
% 7.38/1.50      inference(cnf_transformation,[],[f121]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_1731,plain,
% 7.38/1.50      ( r1_tarski(k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 7.38/1.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_6640,plain,
% 7.38/1.50      ( r1_tarski(k9_relat_1(sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 7.38/1.50      inference(demodulation,[status(thm)],[c_6289,c_1731]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_18113,plain,
% 7.38/1.50      ( k2_relat_1(sK3) = k1_xboole_0
% 7.38/1.50      | r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) != iProver_top ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_17406,c_6640]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_1,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f123]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_1756,plain,
% 7.38/1.50      ( r1_tarski(X0,X0) = iProver_top ),
% 7.38/1.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_30,plain,
% 7.38/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.38/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 7.38/1.50      | ~ r1_tarski(k2_relat_1(X0),X3) ),
% 7.38/1.50      inference(cnf_transformation,[],[f105]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_1732,plain,
% 7.38/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.38/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) = iProver_top
% 7.38/1.50      | r1_tarski(k2_relat_1(X0),X3) != iProver_top ),
% 7.38/1.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_2165,plain,
% 7.38/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0))) = iProver_top
% 7.38/1.50      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_1730,c_1732]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_6291,plain,
% 7.38/1.50      ( k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0,sK3,X1) = k9_relat_1(sK3,X1)
% 7.38/1.50      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_2165,c_1734]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_6785,plain,
% 7.38/1.50      ( k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_relat_1(sK3),sK3,X0) = k9_relat_1(sK3,X0) ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_1756,c_6291]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_26,plain,
% 7.38/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.38/1.50      | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
% 7.38/1.50      inference(cnf_transformation,[],[f101]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_1736,plain,
% 7.38/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.38/1.50      | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) = iProver_top ),
% 7.38/1.50      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_7854,plain,
% 7.38/1.50      ( m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(k2_relat_1(sK3))) = iProver_top
% 7.38/1.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_relat_1(sK3)))) != iProver_top ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_6785,c_1736]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_2046,plain,
% 7.38/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.38/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
% 7.38/1.50      | ~ r1_tarski(k2_relat_1(X0),k2_relat_1(X0)) ),
% 7.38/1.50      inference(instantiation,[status(thm)],[c_30]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_2588,plain,
% 7.38/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_relat_1(sK3))))
% 7.38/1.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))
% 7.38/1.50      | ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(sK3)) ),
% 7.38/1.50      inference(instantiation,[status(thm)],[c_2046]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_2589,plain,
% 7.38/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_relat_1(sK3)))) = iProver_top
% 7.38/1.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) != iProver_top
% 7.38/1.50      | r1_tarski(k2_relat_1(sK3),k2_relat_1(sK3)) != iProver_top ),
% 7.38/1.50      inference(predicate_to_equality,[status(thm)],[c_2588]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_2047,plain,
% 7.38/1.50      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X0)) ),
% 7.38/1.50      inference(instantiation,[status(thm)],[c_1]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_2731,plain,
% 7.38/1.50      ( r1_tarski(k2_relat_1(sK3),k2_relat_1(sK3)) ),
% 7.38/1.50      inference(instantiation,[status(thm)],[c_2047]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_2732,plain,
% 7.38/1.50      ( r1_tarski(k2_relat_1(sK3),k2_relat_1(sK3)) = iProver_top ),
% 7.38/1.50      inference(predicate_to_equality,[status(thm)],[c_2731]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_12099,plain,
% 7.38/1.50      ( m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(k2_relat_1(sK3))) = iProver_top ),
% 7.38/1.50      inference(global_propositional_subsumption,
% 7.38/1.50                [status(thm)],
% 7.38/1.50                [c_7854,c_36,c_2589,c_2732]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_12109,plain,
% 7.38/1.50      ( r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3)) = iProver_top ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_12099,c_1750]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_18212,plain,
% 7.38/1.50      ( k2_relat_1(sK3) = k1_xboole_0 ),
% 7.38/1.50      inference(forward_subsumption_resolution,[status(thm)],[c_18113,c_12109]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_18250,plain,
% 7.38/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0))) = iProver_top
% 7.38/1.50      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 7.38/1.50      inference(demodulation,[status(thm)],[c_18212,c_2165]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_3,plain,
% 7.38/1.50      ( r1_tarski(k1_xboole_0,X0) ),
% 7.38/1.50      inference(cnf_transformation,[],[f71]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_105,plain,
% 7.38/1.50      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.38/1.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_18471,plain,
% 7.38/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0))) = iProver_top ),
% 7.38/1.50      inference(global_propositional_subsumption,[status(thm)],[c_18250,c_105]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_18478,plain,
% 7.38/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_4,c_18471]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_5,plain,
% 7.38/1.50      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.38/1.50      inference(cnf_transformation,[],[f126]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_6294,plain,
% 7.38/1.50      ( k7_relset_1(k1_xboole_0,X0,X1,X2) = k9_relat_1(X1,X2)
% 7.38/1.50      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_5,c_1734]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_18891,plain,
% 7.38/1.50      ( k7_relset_1(k1_xboole_0,X0,sK3,X1) = k9_relat_1(sK3,X1) ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_18478,c_6294]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_3283,plain,
% 7.38/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.38/1.50      | r1_tarski(k7_relset_1(X1,X2,X0,X3),X2) = iProver_top ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_1736,c_1750]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_25799,plain,
% 7.38/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
% 7.38/1.50      | r1_tarski(k9_relat_1(sK3,X1),X0) = iProver_top ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_18891,c_3283]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_25831,plain,
% 7.38/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.38/1.50      | r1_tarski(k9_relat_1(sK3,X0),X1) = iProver_top ),
% 7.38/1.50      inference(light_normalisation,[status(thm)],[c_25799,c_5]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_2129,plain,
% 7.38/1.50      ( v4_relat_1(sK3,X0) != iProver_top
% 7.38/1.50      | r1_tarski(k1_relat_1(sK3),X0) = iProver_top
% 7.38/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.38/1.50      inference(predicate_to_equality,[status(thm)],[c_2117]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_29,plain,
% 7.38/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.38/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 7.38/1.50      | ~ r1_tarski(k1_relat_1(X0),X3) ),
% 7.38/1.50      inference(cnf_transformation,[],[f104]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_2737,plain,
% 7.38/1.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.38/1.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X1)))
% 7.38/1.50      | ~ r1_tarski(k1_relat_1(sK3),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
% 7.38/1.50      inference(instantiation,[status(thm)],[c_29]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_2738,plain,
% 7.38/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.38/1.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X1))) = iProver_top
% 7.38/1.50      | r1_tarski(k1_relat_1(sK3),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != iProver_top ),
% 7.38/1.50      inference(predicate_to_equality,[status(thm)],[c_2737]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_3244,plain,
% 7.38/1.50      ( ~ m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(X1))
% 7.38/1.50      | r1_tarski(k9_relat_1(sK3,X0),X1) ),
% 7.38/1.50      inference(instantiation,[status(thm)],[c_11]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_3245,plain,
% 7.38/1.50      ( m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(X1)) != iProver_top
% 7.38/1.50      | r1_tarski(k9_relat_1(sK3,X0),X1) = iProver_top ),
% 7.38/1.50      inference(predicate_to_equality,[status(thm)],[c_3244]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_1733,plain,
% 7.38/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.38/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
% 7.38/1.50      | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
% 7.38/1.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_18484,plain,
% 7.38/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
% 7.38/1.50      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_18471,c_1733]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_2833,plain,
% 7.38/1.50      ( v4_relat_1(X0,X1) = iProver_top
% 7.38/1.50      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_4,c_1738]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_18889,plain,
% 7.38/1.50      ( v4_relat_1(sK3,X0) = iProver_top ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_18478,c_2833]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_18481,plain,
% 7.38/1.50      ( k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0,sK3,X1) = k9_relat_1(sK3,X1) ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_18471,c_1734]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_20647,plain,
% 7.38/1.50      ( m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(X1)) = iProver_top
% 7.38/1.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X1))) != iProver_top ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_18481,c_1736]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_26281,plain,
% 7.38/1.50      ( r1_tarski(k9_relat_1(sK3,X0),X1) = iProver_top ),
% 7.38/1.50      inference(global_propositional_subsumption,
% 7.38/1.50                [status(thm)],
% 7.38/1.50                [c_25831,c_36,c_1984,c_1996,c_2129,c_2312,c_2738,c_3245,
% 7.38/1.50                 c_18484,c_18889,c_20647]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_26299,plain,
% 7.38/1.50      ( $false ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_26281,c_6640]) ).
% 7.38/1.50  
% 7.38/1.50  
% 7.38/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.38/1.50  
% 7.38/1.50  ------                               Statistics
% 7.38/1.50  
% 7.38/1.50  ------ General
% 7.38/1.50  
% 7.38/1.50  abstr_ref_over_cycles:                  0
% 7.38/1.50  abstr_ref_under_cycles:                 0
% 7.38/1.50  gc_basic_clause_elim:                   0
% 7.38/1.50  forced_gc_time:                         0
% 7.38/1.50  parsing_time:                           0.012
% 7.38/1.50  unif_index_cands_time:                  0.
% 7.38/1.50  unif_index_add_time:                    0.
% 7.38/1.50  orderings_time:                         0.
% 7.38/1.50  out_proof_time:                         0.018
% 7.38/1.50  total_time:                             0.745
% 7.38/1.50  num_of_symbols:                         53
% 7.38/1.50  num_of_terms:                           27231
% 7.38/1.50  
% 7.38/1.50  ------ Preprocessing
% 7.38/1.50  
% 7.38/1.50  num_of_splits:                          0
% 7.38/1.50  num_of_split_atoms:                     0
% 7.38/1.50  num_of_reused_defs:                     0
% 7.38/1.50  num_eq_ax_congr_red:                    35
% 7.38/1.50  num_of_sem_filtered_clauses:            1
% 7.38/1.50  num_of_subtypes:                        0
% 7.38/1.50  monotx_restored_types:                  0
% 7.38/1.50  sat_num_of_epr_types:                   0
% 7.38/1.50  sat_num_of_non_cyclic_types:            0
% 7.38/1.50  sat_guarded_non_collapsed_types:        0
% 7.38/1.50  num_pure_diseq_elim:                    0
% 7.38/1.50  simp_replaced_by:                       0
% 7.38/1.50  res_preprocessed:                       162
% 7.38/1.50  prep_upred:                             0
% 7.38/1.50  prep_unflattend:                        7
% 7.38/1.50  smt_new_axioms:                         0
% 7.38/1.50  pred_elim_cands:                        5
% 7.38/1.50  pred_elim:                              1
% 7.38/1.50  pred_elim_cl:                           1
% 7.38/1.50  pred_elim_cycles:                       3
% 7.38/1.50  merged_defs:                            8
% 7.38/1.50  merged_defs_ncl:                        0
% 7.38/1.50  bin_hyper_res:                          8
% 7.38/1.50  prep_cycles:                            4
% 7.38/1.50  pred_elim_time:                         0.006
% 7.38/1.50  splitting_time:                         0.
% 7.38/1.50  sem_filter_time:                        0.
% 7.38/1.50  monotx_time:                            0.
% 7.38/1.50  subtype_inf_time:                       0.
% 7.38/1.50  
% 7.38/1.50  ------ Problem properties
% 7.38/1.50  
% 7.38/1.50  clauses:                                33
% 7.38/1.50  conjectures:                            3
% 7.38/1.50  epr:                                    5
% 7.38/1.50  horn:                                   31
% 7.38/1.50  ground:                                 3
% 7.38/1.50  unary:                                  7
% 7.38/1.50  binary:                                 12
% 7.38/1.50  lits:                                   74
% 7.38/1.50  lits_eq:                                20
% 7.38/1.50  fd_pure:                                0
% 7.38/1.50  fd_pseudo:                              0
% 7.38/1.50  fd_cond:                                1
% 7.38/1.50  fd_pseudo_cond:                         1
% 7.38/1.50  ac_symbols:                             0
% 7.38/1.50  
% 7.38/1.50  ------ Propositional Solver
% 7.38/1.50  
% 7.38/1.50  prop_solver_calls:                      30
% 7.38/1.50  prop_fast_solver_calls:                 1429
% 7.38/1.50  smt_solver_calls:                       0
% 7.38/1.50  smt_fast_solver_calls:                  0
% 7.38/1.50  prop_num_of_clauses:                    10854
% 7.38/1.50  prop_preprocess_simplified:             19285
% 7.38/1.50  prop_fo_subsumed:                       33
% 7.38/1.50  prop_solver_time:                       0.
% 7.38/1.50  smt_solver_time:                        0.
% 7.38/1.50  smt_fast_solver_time:                   0.
% 7.38/1.50  prop_fast_solver_time:                  0.
% 7.38/1.50  prop_unsat_core_time:                   0.
% 7.38/1.50  
% 7.38/1.50  ------ QBF
% 7.38/1.50  
% 7.38/1.50  qbf_q_res:                              0
% 7.38/1.50  qbf_num_tautologies:                    0
% 7.38/1.50  qbf_prep_cycles:                        0
% 7.38/1.50  
% 7.38/1.50  ------ BMC1
% 7.38/1.50  
% 7.38/1.50  bmc1_current_bound:                     -1
% 7.38/1.50  bmc1_last_solved_bound:                 -1
% 7.38/1.50  bmc1_unsat_core_size:                   -1
% 7.38/1.50  bmc1_unsat_core_parents_size:           -1
% 7.38/1.50  bmc1_merge_next_fun:                    0
% 7.38/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.38/1.50  
% 7.38/1.50  ------ Instantiation
% 7.38/1.50  
% 7.38/1.50  inst_num_of_clauses:                    2794
% 7.38/1.50  inst_num_in_passive:                    360
% 7.38/1.50  inst_num_in_active:                     1270
% 7.38/1.50  inst_num_in_unprocessed:                1167
% 7.38/1.50  inst_num_of_loops:                      1310
% 7.38/1.50  inst_num_of_learning_restarts:          0
% 7.38/1.50  inst_num_moves_active_passive:          36
% 7.38/1.50  inst_lit_activity:                      0
% 7.38/1.50  inst_lit_activity_moves:                0
% 7.38/1.50  inst_num_tautologies:                   0
% 7.38/1.50  inst_num_prop_implied:                  0
% 7.38/1.50  inst_num_existing_simplified:           0
% 7.38/1.50  inst_num_eq_res_simplified:             0
% 7.38/1.50  inst_num_child_elim:                    0
% 7.38/1.50  inst_num_of_dismatching_blockings:      1664
% 7.38/1.50  inst_num_of_non_proper_insts:           4062
% 7.38/1.50  inst_num_of_duplicates:                 0
% 7.38/1.50  inst_inst_num_from_inst_to_res:         0
% 7.38/1.50  inst_dismatching_checking_time:         0.
% 7.38/1.50  
% 7.38/1.50  ------ Resolution
% 7.38/1.50  
% 7.38/1.50  res_num_of_clauses:                     0
% 7.38/1.50  res_num_in_passive:                     0
% 7.38/1.50  res_num_in_active:                      0
% 7.38/1.50  res_num_of_loops:                       166
% 7.38/1.50  res_forward_subset_subsumed:            357
% 7.38/1.50  res_backward_subset_subsumed:           12
% 7.38/1.50  res_forward_subsumed:                   0
% 7.38/1.50  res_backward_subsumed:                  0
% 7.38/1.50  res_forward_subsumption_resolution:     0
% 7.38/1.50  res_backward_subsumption_resolution:    0
% 7.38/1.50  res_clause_to_clause_subsumption:       3164
% 7.38/1.50  res_orphan_elimination:                 0
% 7.38/1.50  res_tautology_del:                      303
% 7.38/1.50  res_num_eq_res_simplified:              0
% 7.38/1.50  res_num_sel_changes:                    0
% 7.38/1.50  res_moves_from_active_to_pass:          0
% 7.38/1.50  
% 7.38/1.50  ------ Superposition
% 7.38/1.50  
% 7.38/1.50  sup_time_total:                         0.
% 7.38/1.50  sup_time_generating:                    0.
% 7.38/1.50  sup_time_sim_full:                      0.
% 7.38/1.50  sup_time_sim_immed:                     0.
% 7.38/1.50  
% 7.38/1.50  sup_num_of_clauses:                     700
% 7.38/1.50  sup_num_in_active:                      178
% 7.38/1.50  sup_num_in_passive:                     522
% 7.38/1.50  sup_num_of_loops:                       261
% 7.38/1.50  sup_fw_superposition:                   509
% 7.38/1.50  sup_bw_superposition:                   647
% 7.38/1.50  sup_immediate_simplified:               646
% 7.38/1.50  sup_given_eliminated:                   0
% 7.38/1.50  comparisons_done:                       0
% 7.38/1.50  comparisons_avoided:                    9
% 7.38/1.50  
% 7.38/1.50  ------ Simplifications
% 7.38/1.50  
% 7.38/1.50  
% 7.38/1.50  sim_fw_subset_subsumed:                 65
% 7.38/1.50  sim_bw_subset_subsumed:                 65
% 7.38/1.50  sim_fw_subsumed:                        38
% 7.38/1.50  sim_bw_subsumed:                        8
% 7.38/1.50  sim_fw_subsumption_res:                 2
% 7.38/1.50  sim_bw_subsumption_res:                 0
% 7.38/1.50  sim_tautology_del:                      7
% 7.38/1.50  sim_eq_tautology_del:                   4
% 7.38/1.50  sim_eq_res_simp:                        1
% 7.38/1.50  sim_fw_demodulated:                     145
% 7.38/1.50  sim_bw_demodulated:                     430
% 7.38/1.50  sim_light_normalised:                   29
% 7.38/1.50  sim_joinable_taut:                      0
% 7.38/1.50  sim_joinable_simp:                      0
% 7.38/1.50  sim_ac_normalised:                      0
% 7.38/1.50  sim_smt_subsumption:                    0
% 7.38/1.50  
%------------------------------------------------------------------------------
