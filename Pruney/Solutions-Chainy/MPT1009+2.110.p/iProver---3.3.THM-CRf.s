%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:50 EST 2020

% Result     : Theorem 11.54s
% Output     : CNFRefutation 11.54s
% Verified   : 
% Statistics : Number of formulae       :  196 ( 943 expanded)
%              Number of clauses        :  104 ( 295 expanded)
%              Number of leaves         :   24 ( 203 expanded)
%              Depth                    :   27
%              Number of atoms          :  541 (2275 expanded)
%              Number of equality atoms :  270 ( 972 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f22,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f24,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(pure_predicate_removal,[],[f23])).

fof(f41,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f42,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f41])).

fof(f57,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
        & k1_xboole_0 != X1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1)))
      & k1_xboole_0 != sK2
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1)))
    & k1_xboole_0 != sK2
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f42,f57])).

fof(f97,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) ),
    inference(cnf_transformation,[],[f58])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f100,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f69,f70])).

fof(f101,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f68,f100])).

fof(f113,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
    inference(definition_unfolding,[],[f97,f101])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f50])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f110,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f71,f101,f101])).

fof(f14,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f86,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f81,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f99,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1))) ),
    inference(cnf_transformation,[],[f58])).

fof(f112,plain,(
    ~ r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) ),
    inference(definition_unfolding,[],[f99,f101,f101])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
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

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f48,plain,(
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

fof(f49,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f47,f48])).

fof(f64,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f105,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f64,f100])).

fof(f116,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f105])).

fof(f117,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_enumset1(X0,X0,X0,X4)) ),
    inference(equality_resolution,[],[f116])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r2_hidden(X1,k1_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) )
       => k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( k2_enumset1(k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_enumset1(X0,X0,X0,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f90,f100,f100])).

fof(f96,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f58])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f21,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_1(X0) ) ) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f39,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f40,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f95,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f43])).

fof(f61,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f52])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f124,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f75])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f123,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f76])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_15,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1508,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1506,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2775,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1508,c_1506])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_1495,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_30,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1498,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_3644,plain,
    ( v4_relat_1(sK4,k2_enumset1(sK1,sK1,sK1,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1495,c_1498])).

cnf(c_21,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1503,plain,
    ( v4_relat_1(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1509,plain,
    ( k2_enumset1(X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_6094,plain,
    ( k2_enumset1(X0,X0,X0,X0) = k1_relat_1(X1)
    | k1_relat_1(X1) = k1_xboole_0
    | v4_relat_1(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1503,c_1509])).

cnf(c_15008,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK4)
    | k1_relat_1(sK4) = k1_xboole_0
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3644,c_6094])).

cnf(c_24,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1502,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2776,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1495,c_1506])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_16,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_269,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_16])).

cnf(c_270,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_269])).

cnf(c_332,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_19,c_270])).

cnf(c_1494,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_332])).

cnf(c_2900,plain,
    ( v1_relat_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2776,c_1494])).

cnf(c_3136,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1502,c_2900])).

cnf(c_15240,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15008,c_3136])).

cnf(c_15241,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK4)
    | k1_relat_1(sK4) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_15240])).

cnf(c_15249,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = X0
    | k1_relat_1(sK4) = k1_xboole_0
    | k1_xboole_0 = X0
    | r1_tarski(X0,k1_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15241,c_1509])).

cnf(c_34,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_40,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_31,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1736,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))
    | k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3) = k9_relat_1(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_855,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1555,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)))
    | k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3) != X0
    | k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) != X1 ),
    inference(instantiation,[status(thm)],[c_855])).

cnf(c_1650,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)))
    | ~ r1_tarski(k9_relat_1(sK4,sK3),X0)
    | k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3) != k9_relat_1(sK4,sK3)
    | k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) != X0 ),
    inference(instantiation,[status(thm)],[c_1555])).

cnf(c_1987,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)))
    | ~ r1_tarski(k9_relat_1(sK4,sK3),k2_relat_1(sK4))
    | k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3) != k9_relat_1(sK4,sK3)
    | k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) != k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1650])).

cnf(c_1988,plain,
    ( k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3) != k9_relat_1(sK4,sK3)
    | k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) != k2_relat_1(sK4)
    | r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) = iProver_top
    | r1_tarski(k9_relat_1(sK4,sK3),k2_relat_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1987])).

cnf(c_25,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2395,plain,
    ( r1_tarski(k9_relat_1(sK4,sK3),k2_relat_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_2396,plain,
    ( r1_tarski(k9_relat_1(sK4,sK3),k2_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2395])).

cnf(c_6,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_1514,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_15245,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | r2_hidden(sK1,k1_relat_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_15241,c_1514])).

cnf(c_28,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k2_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X0)) = k9_relat_1(X1,k2_enumset1(X2,X2,X2,X0)) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_444,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k2_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X0)) = k9_relat_1(X1,k2_enumset1(X2,X2,X2,X0))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_37])).

cnf(c_445,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | ~ r2_hidden(X1,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X1)) = k9_relat_1(sK4,k2_enumset1(X0,X0,X0,X1)) ),
    inference(unflattening,[status(thm)],[c_444])).

cnf(c_1493,plain,
    ( k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X1)) = k9_relat_1(sK4,k2_enumset1(X0,X0,X0,X1))
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(X1,k1_relat_1(sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_445])).

cnf(c_16452,plain,
    ( k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,X0)) = k9_relat_1(sK4,k2_enumset1(sK1,sK1,sK1,X0))
    | k1_relat_1(sK4) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_15245,c_1493])).

cnf(c_16950,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | k1_relat_1(sK4) = k1_xboole_0
    | k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,X0)) = k9_relat_1(sK4,k2_enumset1(sK1,sK1,sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16452,c_3136])).

cnf(c_16951,plain,
    ( k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,X0)) = k9_relat_1(sK4,k2_enumset1(sK1,sK1,sK1,X0))
    | k1_relat_1(sK4) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_16950])).

cnf(c_16958,plain,
    ( k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) = k9_relat_1(sK4,k2_enumset1(sK1,sK1,sK1,sK1))
    | k1_relat_1(sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_15245,c_16951])).

cnf(c_27,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1499,plain,
    ( k7_relat_1(X0,X1) = X0
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_5041,plain,
    ( k7_relat_1(sK4,k2_enumset1(sK1,sK1,sK1,sK1)) = sK4
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3644,c_1499])).

cnf(c_5181,plain,
    ( k7_relat_1(sK4,k2_enumset1(sK1,sK1,sK1,sK1)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5041,c_3136])).

cnf(c_26,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1500,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3383,plain,
    ( k2_relat_1(k7_relat_1(sK4,X0)) = k9_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_3136,c_1500])).

cnf(c_5186,plain,
    ( k9_relat_1(sK4,k2_enumset1(sK1,sK1,sK1,sK1)) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_5181,c_3383])).

cnf(c_16960,plain,
    ( k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) = k2_relat_1(sK4)
    | k1_relat_1(sK4) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_16958,c_5186])).

cnf(c_17818,plain,
    ( k1_relat_1(sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_15249,c_36,c_40,c_1736,c_1988,c_2396,c_3136,c_16960])).

cnf(c_32,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_462,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_37])).

cnf(c_463,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4))))
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_462])).

cnf(c_1492,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4)))) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_463])).

cnf(c_2777,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4))) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1492,c_1506])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1519,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3778,plain,
    ( k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4)) = sK4
    | r1_tarski(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4)),sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2777,c_1519])).

cnf(c_4646,plain,
    ( r1_tarski(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4)),sK4) != iProver_top
    | k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3778,c_3136])).

cnf(c_4647,plain,
    ( k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4)) = sK4
    | r1_tarski(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4)),sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_4646])).

cnf(c_17890,plain,
    ( k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4)) = sK4
    | r1_tarski(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4)),sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_17818,c_4647])).

cnf(c_13,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f124])).

cnf(c_17898,plain,
    ( sK4 = k1_xboole_0
    | r1_tarski(k1_xboole_0,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_17890,c_13])).

cnf(c_18054,plain,
    ( sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2775,c_17898])).

cnf(c_1497,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3536,plain,
    ( k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,X0) = k9_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_1495,c_1497])).

cnf(c_1496,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_3968,plain,
    ( r1_tarski(k9_relat_1(sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3536,c_1496])).

cnf(c_18960,plain,
    ( r1_tarski(k9_relat_1(k1_xboole_0,sK3),k2_enumset1(k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_18054,c_3968])).

cnf(c_3642,plain,
    ( v4_relat_1(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1508,c_1498])).

cnf(c_6567,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3642,c_1499])).

cnf(c_12,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f123])).

cnf(c_2209,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_1502])).

cnf(c_2211,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2209])).

cnf(c_3648,plain,
    ( v4_relat_1(k1_xboole_0,X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3642])).

cnf(c_3667,plain,
    ( ~ v4_relat_1(k1_xboole_0,X0)
    | ~ v1_relat_1(k1_xboole_0)
    | k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_7742,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6567,c_2211,c_3648,c_3667])).

cnf(c_3017,plain,
    ( k2_relat_1(k7_relat_1(k1_xboole_0,X0)) = k9_relat_1(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_2209,c_1500])).

cnf(c_7745,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_7742,c_3017])).

cnf(c_29,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_23,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_480,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_29,c_23])).

cnf(c_1491,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_480])).

cnf(c_2275,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),X0) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1508,c_1491])).

cnf(c_2627,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2275,c_2209])).

cnf(c_6400,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2775,c_1519])).

cnf(c_7193,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2627,c_6400])).

cnf(c_7746,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7745,c_7193])).

cnf(c_18981,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_18960,c_7746])).

cnf(c_23239,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_2775,c_18981])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:02:04 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.54/1.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.54/1.97  
% 11.54/1.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.54/1.97  
% 11.54/1.97  ------  iProver source info
% 11.54/1.97  
% 11.54/1.97  git: date: 2020-06-30 10:37:57 +0100
% 11.54/1.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.54/1.97  git: non_committed_changes: false
% 11.54/1.97  git: last_make_outside_of_git: false
% 11.54/1.97  
% 11.54/1.97  ------ 
% 11.54/1.97  
% 11.54/1.97  ------ Input Options
% 11.54/1.97  
% 11.54/1.97  --out_options                           all
% 11.54/1.97  --tptp_safe_out                         true
% 11.54/1.97  --problem_path                          ""
% 11.54/1.97  --include_path                          ""
% 11.54/1.97  --clausifier                            res/vclausify_rel
% 11.54/1.97  --clausifier_options                    ""
% 11.54/1.97  --stdin                                 false
% 11.54/1.97  --stats_out                             all
% 11.54/1.97  
% 11.54/1.97  ------ General Options
% 11.54/1.97  
% 11.54/1.97  --fof                                   false
% 11.54/1.97  --time_out_real                         305.
% 11.54/1.97  --time_out_virtual                      -1.
% 11.54/1.97  --symbol_type_check                     false
% 11.54/1.97  --clausify_out                          false
% 11.54/1.97  --sig_cnt_out                           false
% 11.54/1.97  --trig_cnt_out                          false
% 11.54/1.97  --trig_cnt_out_tolerance                1.
% 11.54/1.97  --trig_cnt_out_sk_spl                   false
% 11.54/1.97  --abstr_cl_out                          false
% 11.54/1.97  
% 11.54/1.97  ------ Global Options
% 11.54/1.97  
% 11.54/1.97  --schedule                              default
% 11.54/1.97  --add_important_lit                     false
% 11.54/1.97  --prop_solver_per_cl                    1000
% 11.54/1.97  --min_unsat_core                        false
% 11.54/1.97  --soft_assumptions                      false
% 11.54/1.97  --soft_lemma_size                       3
% 11.54/1.97  --prop_impl_unit_size                   0
% 11.54/1.97  --prop_impl_unit                        []
% 11.54/1.97  --share_sel_clauses                     true
% 11.54/1.97  --reset_solvers                         false
% 11.54/1.97  --bc_imp_inh                            [conj_cone]
% 11.54/1.97  --conj_cone_tolerance                   3.
% 11.54/1.97  --extra_neg_conj                        none
% 11.54/1.97  --large_theory_mode                     true
% 11.54/1.97  --prolific_symb_bound                   200
% 11.54/1.97  --lt_threshold                          2000
% 11.54/1.97  --clause_weak_htbl                      true
% 11.54/1.97  --gc_record_bc_elim                     false
% 11.54/1.97  
% 11.54/1.97  ------ Preprocessing Options
% 11.54/1.97  
% 11.54/1.97  --preprocessing_flag                    true
% 11.54/1.97  --time_out_prep_mult                    0.1
% 11.54/1.97  --splitting_mode                        input
% 11.54/1.97  --splitting_grd                         true
% 11.54/1.97  --splitting_cvd                         false
% 11.54/1.97  --splitting_cvd_svl                     false
% 11.54/1.97  --splitting_nvd                         32
% 11.54/1.97  --sub_typing                            true
% 11.54/1.97  --prep_gs_sim                           true
% 11.54/1.97  --prep_unflatten                        true
% 11.54/1.97  --prep_res_sim                          true
% 11.54/1.97  --prep_upred                            true
% 11.54/1.97  --prep_sem_filter                       exhaustive
% 11.54/1.97  --prep_sem_filter_out                   false
% 11.54/1.97  --pred_elim                             true
% 11.54/1.97  --res_sim_input                         true
% 11.54/1.97  --eq_ax_congr_red                       true
% 11.54/1.97  --pure_diseq_elim                       true
% 11.54/1.97  --brand_transform                       false
% 11.54/1.97  --non_eq_to_eq                          false
% 11.54/1.97  --prep_def_merge                        true
% 11.54/1.97  --prep_def_merge_prop_impl              false
% 11.54/1.97  --prep_def_merge_mbd                    true
% 11.54/1.97  --prep_def_merge_tr_red                 false
% 11.54/1.97  --prep_def_merge_tr_cl                  false
% 11.54/1.97  --smt_preprocessing                     true
% 11.54/1.97  --smt_ac_axioms                         fast
% 11.54/1.97  --preprocessed_out                      false
% 11.54/1.97  --preprocessed_stats                    false
% 11.54/1.97  
% 11.54/1.97  ------ Abstraction refinement Options
% 11.54/1.97  
% 11.54/1.97  --abstr_ref                             []
% 11.54/1.97  --abstr_ref_prep                        false
% 11.54/1.97  --abstr_ref_until_sat                   false
% 11.54/1.97  --abstr_ref_sig_restrict                funpre
% 11.54/1.97  --abstr_ref_af_restrict_to_split_sk     false
% 11.54/1.97  --abstr_ref_under                       []
% 11.54/1.97  
% 11.54/1.97  ------ SAT Options
% 11.54/1.97  
% 11.54/1.97  --sat_mode                              false
% 11.54/1.97  --sat_fm_restart_options                ""
% 11.54/1.97  --sat_gr_def                            false
% 11.54/1.97  --sat_epr_types                         true
% 11.54/1.97  --sat_non_cyclic_types                  false
% 11.54/1.97  --sat_finite_models                     false
% 11.54/1.97  --sat_fm_lemmas                         false
% 11.54/1.97  --sat_fm_prep                           false
% 11.54/1.97  --sat_fm_uc_incr                        true
% 11.54/1.97  --sat_out_model                         small
% 11.54/1.97  --sat_out_clauses                       false
% 11.54/1.97  
% 11.54/1.97  ------ QBF Options
% 11.54/1.97  
% 11.54/1.97  --qbf_mode                              false
% 11.54/1.97  --qbf_elim_univ                         false
% 11.54/1.97  --qbf_dom_inst                          none
% 11.54/1.97  --qbf_dom_pre_inst                      false
% 11.54/1.97  --qbf_sk_in                             false
% 11.54/1.97  --qbf_pred_elim                         true
% 11.54/1.97  --qbf_split                             512
% 11.54/1.97  
% 11.54/1.97  ------ BMC1 Options
% 11.54/1.97  
% 11.54/1.97  --bmc1_incremental                      false
% 11.54/1.97  --bmc1_axioms                           reachable_all
% 11.54/1.97  --bmc1_min_bound                        0
% 11.54/1.97  --bmc1_max_bound                        -1
% 11.54/1.97  --bmc1_max_bound_default                -1
% 11.54/1.97  --bmc1_symbol_reachability              true
% 11.54/1.97  --bmc1_property_lemmas                  false
% 11.54/1.97  --bmc1_k_induction                      false
% 11.54/1.97  --bmc1_non_equiv_states                 false
% 11.54/1.97  --bmc1_deadlock                         false
% 11.54/1.97  --bmc1_ucm                              false
% 11.54/1.97  --bmc1_add_unsat_core                   none
% 11.54/1.97  --bmc1_unsat_core_children              false
% 11.54/1.97  --bmc1_unsat_core_extrapolate_axioms    false
% 11.54/1.97  --bmc1_out_stat                         full
% 11.54/1.97  --bmc1_ground_init                      false
% 11.54/1.97  --bmc1_pre_inst_next_state              false
% 11.54/1.97  --bmc1_pre_inst_state                   false
% 11.54/1.97  --bmc1_pre_inst_reach_state             false
% 11.54/1.97  --bmc1_out_unsat_core                   false
% 11.54/1.97  --bmc1_aig_witness_out                  false
% 11.54/1.97  --bmc1_verbose                          false
% 11.54/1.97  --bmc1_dump_clauses_tptp                false
% 11.54/1.97  --bmc1_dump_unsat_core_tptp             false
% 11.54/1.97  --bmc1_dump_file                        -
% 11.54/1.97  --bmc1_ucm_expand_uc_limit              128
% 11.54/1.97  --bmc1_ucm_n_expand_iterations          6
% 11.54/1.97  --bmc1_ucm_extend_mode                  1
% 11.54/1.97  --bmc1_ucm_init_mode                    2
% 11.54/1.97  --bmc1_ucm_cone_mode                    none
% 11.54/1.97  --bmc1_ucm_reduced_relation_type        0
% 11.54/1.97  --bmc1_ucm_relax_model                  4
% 11.54/1.97  --bmc1_ucm_full_tr_after_sat            true
% 11.54/1.97  --bmc1_ucm_expand_neg_assumptions       false
% 11.54/1.97  --bmc1_ucm_layered_model                none
% 11.54/1.97  --bmc1_ucm_max_lemma_size               10
% 11.54/1.97  
% 11.54/1.97  ------ AIG Options
% 11.54/1.97  
% 11.54/1.97  --aig_mode                              false
% 11.54/1.97  
% 11.54/1.97  ------ Instantiation Options
% 11.54/1.97  
% 11.54/1.97  --instantiation_flag                    true
% 11.54/1.97  --inst_sos_flag                         true
% 11.54/1.97  --inst_sos_phase                        true
% 11.54/1.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.54/1.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.54/1.97  --inst_lit_sel_side                     num_symb
% 11.54/1.97  --inst_solver_per_active                1400
% 11.54/1.97  --inst_solver_calls_frac                1.
% 11.54/1.97  --inst_passive_queue_type               priority_queues
% 11.54/1.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.54/1.97  --inst_passive_queues_freq              [25;2]
% 11.54/1.97  --inst_dismatching                      true
% 11.54/1.97  --inst_eager_unprocessed_to_passive     true
% 11.54/1.97  --inst_prop_sim_given                   true
% 11.54/1.97  --inst_prop_sim_new                     false
% 11.54/1.97  --inst_subs_new                         false
% 11.54/1.97  --inst_eq_res_simp                      false
% 11.54/1.97  --inst_subs_given                       false
% 11.54/1.97  --inst_orphan_elimination               true
% 11.54/1.97  --inst_learning_loop_flag               true
% 11.54/1.97  --inst_learning_start                   3000
% 11.54/1.97  --inst_learning_factor                  2
% 11.54/1.97  --inst_start_prop_sim_after_learn       3
% 11.54/1.97  --inst_sel_renew                        solver
% 11.54/1.97  --inst_lit_activity_flag                true
% 11.54/1.97  --inst_restr_to_given                   false
% 11.54/1.97  --inst_activity_threshold               500
% 11.54/1.97  --inst_out_proof                        true
% 11.54/1.97  
% 11.54/1.97  ------ Resolution Options
% 11.54/1.97  
% 11.54/1.97  --resolution_flag                       true
% 11.54/1.97  --res_lit_sel                           adaptive
% 11.54/1.97  --res_lit_sel_side                      none
% 11.54/1.97  --res_ordering                          kbo
% 11.54/1.97  --res_to_prop_solver                    active
% 11.54/1.97  --res_prop_simpl_new                    false
% 11.54/1.97  --res_prop_simpl_given                  true
% 11.54/1.97  --res_passive_queue_type                priority_queues
% 11.54/1.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.54/1.97  --res_passive_queues_freq               [15;5]
% 11.54/1.97  --res_forward_subs                      full
% 11.54/1.97  --res_backward_subs                     full
% 11.54/1.97  --res_forward_subs_resolution           true
% 11.54/1.97  --res_backward_subs_resolution          true
% 11.54/1.97  --res_orphan_elimination                true
% 11.54/1.97  --res_time_limit                        2.
% 11.54/1.97  --res_out_proof                         true
% 11.54/1.97  
% 11.54/1.97  ------ Superposition Options
% 11.54/1.97  
% 11.54/1.97  --superposition_flag                    true
% 11.54/1.97  --sup_passive_queue_type                priority_queues
% 11.54/1.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.54/1.97  --sup_passive_queues_freq               [8;1;4]
% 11.54/1.97  --demod_completeness_check              fast
% 11.54/1.97  --demod_use_ground                      true
% 11.54/1.97  --sup_to_prop_solver                    passive
% 11.54/1.97  --sup_prop_simpl_new                    true
% 11.54/1.97  --sup_prop_simpl_given                  true
% 11.54/1.97  --sup_fun_splitting                     true
% 11.54/1.97  --sup_smt_interval                      50000
% 11.54/1.97  
% 11.54/1.97  ------ Superposition Simplification Setup
% 11.54/1.97  
% 11.54/1.97  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.54/1.97  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.54/1.97  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.54/1.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.54/1.97  --sup_full_triv                         [TrivRules;PropSubs]
% 11.54/1.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.54/1.97  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.54/1.97  --sup_immed_triv                        [TrivRules]
% 11.54/1.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.54/1.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.54/1.97  --sup_immed_bw_main                     []
% 11.54/1.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.54/1.97  --sup_input_triv                        [Unflattening;TrivRules]
% 11.54/1.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.54/1.97  --sup_input_bw                          []
% 11.54/1.97  
% 11.54/1.97  ------ Combination Options
% 11.54/1.97  
% 11.54/1.97  --comb_res_mult                         3
% 11.54/1.97  --comb_sup_mult                         2
% 11.54/1.97  --comb_inst_mult                        10
% 11.54/1.97  
% 11.54/1.97  ------ Debug Options
% 11.54/1.97  
% 11.54/1.97  --dbg_backtrace                         false
% 11.54/1.97  --dbg_dump_prop_clauses                 false
% 11.54/1.97  --dbg_dump_prop_clauses_file            -
% 11.54/1.97  --dbg_out_stat                          false
% 11.54/1.97  ------ Parsing...
% 11.54/1.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.54/1.97  
% 11.54/1.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.54/1.97  
% 11.54/1.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.54/1.97  
% 11.54/1.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.54/1.97  ------ Proving...
% 11.54/1.97  ------ Problem Properties 
% 11.54/1.97  
% 11.54/1.97  
% 11.54/1.97  clauses                                 33
% 11.54/1.97  conjectures                             3
% 11.54/1.97  EPR                                     4
% 11.54/1.97  Horn                                    29
% 11.54/1.97  unary                                   12
% 11.54/1.97  binary                                  7
% 11.54/1.97  lits                                    70
% 11.54/1.97  lits eq                                 22
% 11.54/1.97  fd_pure                                 0
% 11.54/1.97  fd_pseudo                               0
% 11.54/1.97  fd_cond                                 1
% 11.54/1.97  fd_pseudo_cond                          5
% 11.54/1.97  AC symbols                              0
% 11.54/1.97  
% 11.54/1.97  ------ Schedule dynamic 5 is on 
% 11.54/1.97  
% 11.54/1.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.54/1.97  
% 11.54/1.97  
% 11.54/1.97  ------ 
% 11.54/1.97  Current options:
% 11.54/1.97  ------ 
% 11.54/1.97  
% 11.54/1.97  ------ Input Options
% 11.54/1.97  
% 11.54/1.97  --out_options                           all
% 11.54/1.97  --tptp_safe_out                         true
% 11.54/1.97  --problem_path                          ""
% 11.54/1.97  --include_path                          ""
% 11.54/1.97  --clausifier                            res/vclausify_rel
% 11.54/1.97  --clausifier_options                    ""
% 11.54/1.97  --stdin                                 false
% 11.54/1.97  --stats_out                             all
% 11.54/1.97  
% 11.54/1.97  ------ General Options
% 11.54/1.97  
% 11.54/1.97  --fof                                   false
% 11.54/1.97  --time_out_real                         305.
% 11.54/1.97  --time_out_virtual                      -1.
% 11.54/1.97  --symbol_type_check                     false
% 11.54/1.97  --clausify_out                          false
% 11.54/1.97  --sig_cnt_out                           false
% 11.54/1.97  --trig_cnt_out                          false
% 11.54/1.97  --trig_cnt_out_tolerance                1.
% 11.54/1.97  --trig_cnt_out_sk_spl                   false
% 11.54/1.97  --abstr_cl_out                          false
% 11.54/1.97  
% 11.54/1.97  ------ Global Options
% 11.54/1.97  
% 11.54/1.97  --schedule                              default
% 11.54/1.97  --add_important_lit                     false
% 11.54/1.97  --prop_solver_per_cl                    1000
% 11.54/1.97  --min_unsat_core                        false
% 11.54/1.97  --soft_assumptions                      false
% 11.54/1.97  --soft_lemma_size                       3
% 11.54/1.97  --prop_impl_unit_size                   0
% 11.54/1.97  --prop_impl_unit                        []
% 11.54/1.97  --share_sel_clauses                     true
% 11.54/1.97  --reset_solvers                         false
% 11.54/1.97  --bc_imp_inh                            [conj_cone]
% 11.54/1.97  --conj_cone_tolerance                   3.
% 11.54/1.97  --extra_neg_conj                        none
% 11.54/1.97  --large_theory_mode                     true
% 11.54/1.97  --prolific_symb_bound                   200
% 11.54/1.97  --lt_threshold                          2000
% 11.54/1.97  --clause_weak_htbl                      true
% 11.54/1.97  --gc_record_bc_elim                     false
% 11.54/1.97  
% 11.54/1.97  ------ Preprocessing Options
% 11.54/1.97  
% 11.54/1.97  --preprocessing_flag                    true
% 11.54/1.97  --time_out_prep_mult                    0.1
% 11.54/1.97  --splitting_mode                        input
% 11.54/1.97  --splitting_grd                         true
% 11.54/1.97  --splitting_cvd                         false
% 11.54/1.97  --splitting_cvd_svl                     false
% 11.54/1.97  --splitting_nvd                         32
% 11.54/1.97  --sub_typing                            true
% 11.54/1.97  --prep_gs_sim                           true
% 11.54/1.97  --prep_unflatten                        true
% 11.54/1.97  --prep_res_sim                          true
% 11.54/1.97  --prep_upred                            true
% 11.54/1.97  --prep_sem_filter                       exhaustive
% 11.54/1.97  --prep_sem_filter_out                   false
% 11.54/1.97  --pred_elim                             true
% 11.54/1.97  --res_sim_input                         true
% 11.54/1.97  --eq_ax_congr_red                       true
% 11.54/1.97  --pure_diseq_elim                       true
% 11.54/1.97  --brand_transform                       false
% 11.54/1.97  --non_eq_to_eq                          false
% 11.54/1.97  --prep_def_merge                        true
% 11.54/1.97  --prep_def_merge_prop_impl              false
% 11.54/1.97  --prep_def_merge_mbd                    true
% 11.54/1.97  --prep_def_merge_tr_red                 false
% 11.54/1.97  --prep_def_merge_tr_cl                  false
% 11.54/1.97  --smt_preprocessing                     true
% 11.54/1.97  --smt_ac_axioms                         fast
% 11.54/1.97  --preprocessed_out                      false
% 11.54/1.97  --preprocessed_stats                    false
% 11.54/1.97  
% 11.54/1.97  ------ Abstraction refinement Options
% 11.54/1.97  
% 11.54/1.97  --abstr_ref                             []
% 11.54/1.97  --abstr_ref_prep                        false
% 11.54/1.97  --abstr_ref_until_sat                   false
% 11.54/1.97  --abstr_ref_sig_restrict                funpre
% 11.54/1.97  --abstr_ref_af_restrict_to_split_sk     false
% 11.54/1.97  --abstr_ref_under                       []
% 11.54/1.97  
% 11.54/1.97  ------ SAT Options
% 11.54/1.97  
% 11.54/1.97  --sat_mode                              false
% 11.54/1.97  --sat_fm_restart_options                ""
% 11.54/1.97  --sat_gr_def                            false
% 11.54/1.97  --sat_epr_types                         true
% 11.54/1.97  --sat_non_cyclic_types                  false
% 11.54/1.97  --sat_finite_models                     false
% 11.54/1.97  --sat_fm_lemmas                         false
% 11.54/1.97  --sat_fm_prep                           false
% 11.54/1.97  --sat_fm_uc_incr                        true
% 11.54/1.97  --sat_out_model                         small
% 11.54/1.97  --sat_out_clauses                       false
% 11.54/1.97  
% 11.54/1.97  ------ QBF Options
% 11.54/1.97  
% 11.54/1.97  --qbf_mode                              false
% 11.54/1.97  --qbf_elim_univ                         false
% 11.54/1.97  --qbf_dom_inst                          none
% 11.54/1.97  --qbf_dom_pre_inst                      false
% 11.54/1.97  --qbf_sk_in                             false
% 11.54/1.97  --qbf_pred_elim                         true
% 11.54/1.97  --qbf_split                             512
% 11.54/1.97  
% 11.54/1.97  ------ BMC1 Options
% 11.54/1.97  
% 11.54/1.97  --bmc1_incremental                      false
% 11.54/1.97  --bmc1_axioms                           reachable_all
% 11.54/1.97  --bmc1_min_bound                        0
% 11.54/1.97  --bmc1_max_bound                        -1
% 11.54/1.97  --bmc1_max_bound_default                -1
% 11.54/1.97  --bmc1_symbol_reachability              true
% 11.54/1.97  --bmc1_property_lemmas                  false
% 11.54/1.97  --bmc1_k_induction                      false
% 11.54/1.97  --bmc1_non_equiv_states                 false
% 11.54/1.97  --bmc1_deadlock                         false
% 11.54/1.97  --bmc1_ucm                              false
% 11.54/1.97  --bmc1_add_unsat_core                   none
% 11.54/1.97  --bmc1_unsat_core_children              false
% 11.54/1.97  --bmc1_unsat_core_extrapolate_axioms    false
% 11.54/1.97  --bmc1_out_stat                         full
% 11.54/1.97  --bmc1_ground_init                      false
% 11.54/1.97  --bmc1_pre_inst_next_state              false
% 11.54/1.97  --bmc1_pre_inst_state                   false
% 11.54/1.97  --bmc1_pre_inst_reach_state             false
% 11.54/1.97  --bmc1_out_unsat_core                   false
% 11.54/1.97  --bmc1_aig_witness_out                  false
% 11.54/1.97  --bmc1_verbose                          false
% 11.54/1.97  --bmc1_dump_clauses_tptp                false
% 11.54/1.97  --bmc1_dump_unsat_core_tptp             false
% 11.54/1.97  --bmc1_dump_file                        -
% 11.54/1.97  --bmc1_ucm_expand_uc_limit              128
% 11.54/1.97  --bmc1_ucm_n_expand_iterations          6
% 11.54/1.97  --bmc1_ucm_extend_mode                  1
% 11.54/1.97  --bmc1_ucm_init_mode                    2
% 11.54/1.97  --bmc1_ucm_cone_mode                    none
% 11.54/1.97  --bmc1_ucm_reduced_relation_type        0
% 11.54/1.97  --bmc1_ucm_relax_model                  4
% 11.54/1.97  --bmc1_ucm_full_tr_after_sat            true
% 11.54/1.97  --bmc1_ucm_expand_neg_assumptions       false
% 11.54/1.97  --bmc1_ucm_layered_model                none
% 11.54/1.97  --bmc1_ucm_max_lemma_size               10
% 11.54/1.97  
% 11.54/1.97  ------ AIG Options
% 11.54/1.97  
% 11.54/1.97  --aig_mode                              false
% 11.54/1.97  
% 11.54/1.97  ------ Instantiation Options
% 11.54/1.97  
% 11.54/1.97  --instantiation_flag                    true
% 11.54/1.97  --inst_sos_flag                         true
% 11.54/1.97  --inst_sos_phase                        true
% 11.54/1.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.54/1.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.54/1.97  --inst_lit_sel_side                     none
% 11.54/1.97  --inst_solver_per_active                1400
% 11.54/1.97  --inst_solver_calls_frac                1.
% 11.54/1.97  --inst_passive_queue_type               priority_queues
% 11.54/1.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.54/1.97  --inst_passive_queues_freq              [25;2]
% 11.54/1.97  --inst_dismatching                      true
% 11.54/1.97  --inst_eager_unprocessed_to_passive     true
% 11.54/1.97  --inst_prop_sim_given                   true
% 11.54/1.97  --inst_prop_sim_new                     false
% 11.54/1.97  --inst_subs_new                         false
% 11.54/1.97  --inst_eq_res_simp                      false
% 11.54/1.97  --inst_subs_given                       false
% 11.54/1.97  --inst_orphan_elimination               true
% 11.54/1.97  --inst_learning_loop_flag               true
% 11.54/1.97  --inst_learning_start                   3000
% 11.54/1.97  --inst_learning_factor                  2
% 11.54/1.97  --inst_start_prop_sim_after_learn       3
% 11.54/1.97  --inst_sel_renew                        solver
% 11.54/1.97  --inst_lit_activity_flag                true
% 11.54/1.97  --inst_restr_to_given                   false
% 11.54/1.97  --inst_activity_threshold               500
% 11.54/1.97  --inst_out_proof                        true
% 11.54/1.97  
% 11.54/1.97  ------ Resolution Options
% 11.54/1.97  
% 11.54/1.97  --resolution_flag                       false
% 11.54/1.97  --res_lit_sel                           adaptive
% 11.54/1.97  --res_lit_sel_side                      none
% 11.54/1.97  --res_ordering                          kbo
% 11.54/1.97  --res_to_prop_solver                    active
% 11.54/1.97  --res_prop_simpl_new                    false
% 11.54/1.97  --res_prop_simpl_given                  true
% 11.54/1.97  --res_passive_queue_type                priority_queues
% 11.54/1.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.54/1.97  --res_passive_queues_freq               [15;5]
% 11.54/1.97  --res_forward_subs                      full
% 11.54/1.97  --res_backward_subs                     full
% 11.54/1.97  --res_forward_subs_resolution           true
% 11.54/1.97  --res_backward_subs_resolution          true
% 11.54/1.97  --res_orphan_elimination                true
% 11.54/1.97  --res_time_limit                        2.
% 11.54/1.97  --res_out_proof                         true
% 11.54/1.97  
% 11.54/1.97  ------ Superposition Options
% 11.54/1.97  
% 11.54/1.97  --superposition_flag                    true
% 11.54/1.97  --sup_passive_queue_type                priority_queues
% 11.54/1.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.54/1.97  --sup_passive_queues_freq               [8;1;4]
% 11.54/1.97  --demod_completeness_check              fast
% 11.54/1.97  --demod_use_ground                      true
% 11.54/1.97  --sup_to_prop_solver                    passive
% 11.54/1.97  --sup_prop_simpl_new                    true
% 11.54/1.97  --sup_prop_simpl_given                  true
% 11.54/1.97  --sup_fun_splitting                     true
% 11.54/1.97  --sup_smt_interval                      50000
% 11.54/1.97  
% 11.54/1.97  ------ Superposition Simplification Setup
% 11.54/1.97  
% 11.54/1.97  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.54/1.97  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.54/1.97  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.54/1.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.54/1.97  --sup_full_triv                         [TrivRules;PropSubs]
% 11.54/1.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.54/1.97  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.54/1.97  --sup_immed_triv                        [TrivRules]
% 11.54/1.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.54/1.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.54/1.97  --sup_immed_bw_main                     []
% 11.54/1.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.54/1.97  --sup_input_triv                        [Unflattening;TrivRules]
% 11.54/1.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.54/1.97  --sup_input_bw                          []
% 11.54/1.97  
% 11.54/1.97  ------ Combination Options
% 11.54/1.97  
% 11.54/1.97  --comb_res_mult                         3
% 11.54/1.97  --comb_sup_mult                         2
% 11.54/1.97  --comb_inst_mult                        10
% 11.54/1.97  
% 11.54/1.97  ------ Debug Options
% 11.54/1.97  
% 11.54/1.97  --dbg_backtrace                         false
% 11.54/1.97  --dbg_dump_prop_clauses                 false
% 11.54/1.97  --dbg_dump_prop_clauses_file            -
% 11.54/1.97  --dbg_out_stat                          false
% 11.54/1.97  
% 11.54/1.97  
% 11.54/1.97  
% 11.54/1.97  
% 11.54/1.97  ------ Proving...
% 11.54/1.97  
% 11.54/1.97  
% 11.54/1.97  % SZS status Theorem for theBenchmark.p
% 11.54/1.97  
% 11.54/1.97   Resolution empty clause
% 11.54/1.97  
% 11.54/1.97  % SZS output start CNFRefutation for theBenchmark.p
% 11.54/1.97  
% 11.54/1.97  fof(f8,axiom,(
% 11.54/1.97    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 11.54/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.54/1.97  
% 11.54/1.97  fof(f77,plain,(
% 11.54/1.97    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 11.54/1.97    inference(cnf_transformation,[],[f8])).
% 11.54/1.97  
% 11.54/1.97  fof(f9,axiom,(
% 11.54/1.97    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 11.54/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.54/1.97  
% 11.54/1.97  fof(f54,plain,(
% 11.54/1.97    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 11.54/1.97    inference(nnf_transformation,[],[f9])).
% 11.54/1.97  
% 11.54/1.97  fof(f78,plain,(
% 11.54/1.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 11.54/1.97    inference(cnf_transformation,[],[f54])).
% 11.54/1.97  
% 11.54/1.97  fof(f22,conjecture,(
% 11.54/1.97    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 11.54/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.54/1.97  
% 11.54/1.97  fof(f23,negated_conjecture,(
% 11.54/1.97    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 11.54/1.97    inference(negated_conjecture,[],[f22])).
% 11.54/1.97  
% 11.54/1.97  fof(f24,plain,(
% 11.54/1.97    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 11.54/1.97    inference(pure_predicate_removal,[],[f23])).
% 11.54/1.97  
% 11.54/1.97  fof(f41,plain,(
% 11.54/1.97    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 11.54/1.97    inference(ennf_transformation,[],[f24])).
% 11.54/1.97  
% 11.54/1.97  fof(f42,plain,(
% 11.54/1.97    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 11.54/1.97    inference(flattening,[],[f41])).
% 11.54/1.97  
% 11.54/1.97  fof(f57,plain,(
% 11.54/1.97    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1))) & k1_xboole_0 != sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_1(sK4))),
% 11.54/1.97    introduced(choice_axiom,[])).
% 11.54/1.97  
% 11.54/1.97  fof(f58,plain,(
% 11.54/1.97    ~r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1))) & k1_xboole_0 != sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_1(sK4)),
% 11.54/1.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f42,f57])).
% 11.54/1.97  
% 11.54/1.97  fof(f97,plain,(
% 11.54/1.97    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))),
% 11.54/1.97    inference(cnf_transformation,[],[f58])).
% 11.54/1.97  
% 11.54/1.97  fof(f3,axiom,(
% 11.54/1.97    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 11.54/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.54/1.97  
% 11.54/1.97  fof(f68,plain,(
% 11.54/1.97    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 11.54/1.97    inference(cnf_transformation,[],[f3])).
% 11.54/1.97  
% 11.54/1.97  fof(f4,axiom,(
% 11.54/1.97    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 11.54/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.54/1.97  
% 11.54/1.97  fof(f69,plain,(
% 11.54/1.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 11.54/1.97    inference(cnf_transformation,[],[f4])).
% 11.54/1.97  
% 11.54/1.97  fof(f5,axiom,(
% 11.54/1.97    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 11.54/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.54/1.97  
% 11.54/1.97  fof(f70,plain,(
% 11.54/1.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 11.54/1.97    inference(cnf_transformation,[],[f5])).
% 11.54/1.97  
% 11.54/1.97  fof(f100,plain,(
% 11.54/1.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 11.54/1.97    inference(definition_unfolding,[],[f69,f70])).
% 11.54/1.97  
% 11.54/1.97  fof(f101,plain,(
% 11.54/1.97    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 11.54/1.97    inference(definition_unfolding,[],[f68,f100])).
% 11.54/1.97  
% 11.54/1.97  fof(f113,plain,(
% 11.54/1.97    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))),
% 11.54/1.97    inference(definition_unfolding,[],[f97,f101])).
% 11.54/1.97  
% 11.54/1.97  fof(f19,axiom,(
% 11.54/1.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 11.54/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.54/1.97  
% 11.54/1.97  fof(f37,plain,(
% 11.54/1.97    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.54/1.97    inference(ennf_transformation,[],[f19])).
% 11.54/1.97  
% 11.54/1.97  fof(f91,plain,(
% 11.54/1.97    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.54/1.97    inference(cnf_transformation,[],[f37])).
% 11.54/1.97  
% 11.54/1.97  fof(f12,axiom,(
% 11.54/1.97    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 11.54/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.54/1.97  
% 11.54/1.97  fof(f29,plain,(
% 11.54/1.97    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.54/1.97    inference(ennf_transformation,[],[f12])).
% 11.54/1.97  
% 11.54/1.97  fof(f55,plain,(
% 11.54/1.97    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 11.54/1.97    inference(nnf_transformation,[],[f29])).
% 11.54/1.97  
% 11.54/1.97  fof(f82,plain,(
% 11.54/1.97    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.54/1.97    inference(cnf_transformation,[],[f55])).
% 11.54/1.97  
% 11.54/1.97  fof(f6,axiom,(
% 11.54/1.97    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 11.54/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.54/1.97  
% 11.54/1.97  fof(f50,plain,(
% 11.54/1.97    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 11.54/1.97    inference(nnf_transformation,[],[f6])).
% 11.54/1.97  
% 11.54/1.97  fof(f51,plain,(
% 11.54/1.97    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 11.54/1.97    inference(flattening,[],[f50])).
% 11.54/1.97  
% 11.54/1.97  fof(f71,plain,(
% 11.54/1.97    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 11.54/1.97    inference(cnf_transformation,[],[f51])).
% 11.54/1.97  
% 11.54/1.97  fof(f110,plain,(
% 11.54/1.97    ( ! [X0,X1] : (k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))) )),
% 11.54/1.97    inference(definition_unfolding,[],[f71,f101,f101])).
% 11.54/1.97  
% 11.54/1.97  fof(f14,axiom,(
% 11.54/1.97    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 11.54/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.54/1.97  
% 11.54/1.97  fof(f86,plain,(
% 11.54/1.97    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 11.54/1.97    inference(cnf_transformation,[],[f14])).
% 11.54/1.97  
% 11.54/1.97  fof(f11,axiom,(
% 11.54/1.97    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 11.54/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.54/1.97  
% 11.54/1.97  fof(f28,plain,(
% 11.54/1.97    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 11.54/1.97    inference(ennf_transformation,[],[f11])).
% 11.54/1.97  
% 11.54/1.97  fof(f81,plain,(
% 11.54/1.97    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 11.54/1.97    inference(cnf_transformation,[],[f28])).
% 11.54/1.97  
% 11.54/1.97  fof(f79,plain,(
% 11.54/1.97    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 11.54/1.97    inference(cnf_transformation,[],[f54])).
% 11.54/1.97  
% 11.54/1.97  fof(f99,plain,(
% 11.54/1.97    ~r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1)))),
% 11.54/1.97    inference(cnf_transformation,[],[f58])).
% 11.54/1.97  
% 11.54/1.97  fof(f112,plain,(
% 11.54/1.97    ~r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)))),
% 11.54/1.97    inference(definition_unfolding,[],[f99,f101,f101])).
% 11.54/1.97  
% 11.54/1.97  fof(f20,axiom,(
% 11.54/1.97    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 11.54/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.54/1.97  
% 11.54/1.97  fof(f38,plain,(
% 11.54/1.97    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.54/1.97    inference(ennf_transformation,[],[f20])).
% 11.54/1.97  
% 11.54/1.97  fof(f93,plain,(
% 11.54/1.97    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.54/1.97    inference(cnf_transformation,[],[f38])).
% 11.54/1.97  
% 11.54/1.97  fof(f15,axiom,(
% 11.54/1.97    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 11.54/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.54/1.97  
% 11.54/1.97  fof(f31,plain,(
% 11.54/1.97    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 11.54/1.97    inference(ennf_transformation,[],[f15])).
% 11.54/1.97  
% 11.54/1.97  fof(f87,plain,(
% 11.54/1.97    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 11.54/1.97    inference(cnf_transformation,[],[f31])).
% 11.54/1.97  
% 11.54/1.97  fof(f2,axiom,(
% 11.54/1.97    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 11.54/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.54/1.97  
% 11.54/1.97  fof(f45,plain,(
% 11.54/1.97    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 11.54/1.97    inference(nnf_transformation,[],[f2])).
% 11.54/1.97  
% 11.54/1.97  fof(f46,plain,(
% 11.54/1.97    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 11.54/1.97    inference(flattening,[],[f45])).
% 11.54/1.97  
% 11.54/1.97  fof(f47,plain,(
% 11.54/1.97    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 11.54/1.97    inference(rectify,[],[f46])).
% 11.54/1.97  
% 11.54/1.97  fof(f48,plain,(
% 11.54/1.97    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2))))),
% 11.54/1.97    introduced(choice_axiom,[])).
% 11.54/1.97  
% 11.54/1.97  fof(f49,plain,(
% 11.54/1.97    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 11.54/1.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f47,f48])).
% 11.54/1.97  
% 11.54/1.97  fof(f64,plain,(
% 11.54/1.97    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 11.54/1.97    inference(cnf_transformation,[],[f49])).
% 11.54/1.97  
% 11.54/1.97  fof(f105,plain,(
% 11.54/1.97    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 11.54/1.97    inference(definition_unfolding,[],[f64,f100])).
% 11.54/1.97  
% 11.54/1.97  fof(f116,plain,(
% 11.54/1.97    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X4) != X2) )),
% 11.54/1.97    inference(equality_resolution,[],[f105])).
% 11.54/1.97  
% 11.54/1.97  fof(f117,plain,(
% 11.54/1.97    ( ! [X4,X0] : (r2_hidden(X4,k2_enumset1(X0,X0,X0,X4))) )),
% 11.54/1.97    inference(equality_resolution,[],[f116])).
% 11.54/1.97  
% 11.54/1.97  fof(f18,axiom,(
% 11.54/1.97    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r2_hidden(X1,k1_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) => k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1))))),
% 11.54/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.54/1.97  
% 11.54/1.97  fof(f35,plain,(
% 11.54/1.97    ! [X0,X1,X2] : ((k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1)) | (~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 11.54/1.97    inference(ennf_transformation,[],[f18])).
% 11.54/1.97  
% 11.54/1.97  fof(f36,plain,(
% 11.54/1.97    ! [X0,X1,X2] : (k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 11.54/1.97    inference(flattening,[],[f35])).
% 11.54/1.97  
% 11.54/1.97  fof(f90,plain,(
% 11.54/1.97    ( ! [X2,X0,X1] : (k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 11.54/1.97    inference(cnf_transformation,[],[f36])).
% 11.54/1.97  
% 11.54/1.97  fof(f111,plain,(
% 11.54/1.97    ( ! [X2,X0,X1] : (k2_enumset1(k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_enumset1(X0,X0,X0,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 11.54/1.97    inference(definition_unfolding,[],[f90,f100,f100])).
% 11.54/1.97  
% 11.54/1.97  fof(f96,plain,(
% 11.54/1.97    v1_funct_1(sK4)),
% 11.54/1.97    inference(cnf_transformation,[],[f58])).
% 11.54/1.97  
% 11.54/1.97  fof(f17,axiom,(
% 11.54/1.97    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 11.54/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.54/1.97  
% 11.54/1.97  fof(f33,plain,(
% 11.54/1.97    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 11.54/1.97    inference(ennf_transformation,[],[f17])).
% 11.54/1.97  
% 11.54/1.97  fof(f34,plain,(
% 11.54/1.97    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 11.54/1.97    inference(flattening,[],[f33])).
% 11.54/1.97  
% 11.54/1.97  fof(f89,plain,(
% 11.54/1.97    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.54/1.97    inference(cnf_transformation,[],[f34])).
% 11.54/1.97  
% 11.54/1.97  fof(f16,axiom,(
% 11.54/1.97    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 11.54/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.54/1.97  
% 11.54/1.97  fof(f32,plain,(
% 11.54/1.97    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 11.54/1.97    inference(ennf_transformation,[],[f16])).
% 11.54/1.97  
% 11.54/1.97  fof(f88,plain,(
% 11.54/1.97    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.54/1.97    inference(cnf_transformation,[],[f32])).
% 11.54/1.97  
% 11.54/1.97  fof(f21,axiom,(
% 11.54/1.97    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 11.54/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.54/1.97  
% 11.54/1.97  fof(f25,plain,(
% 11.54/1.97    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_1(X0)))),
% 11.54/1.97    inference(pure_predicate_removal,[],[f21])).
% 11.54/1.97  
% 11.54/1.97  fof(f39,plain,(
% 11.54/1.97    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.54/1.97    inference(ennf_transformation,[],[f25])).
% 11.54/1.97  
% 11.54/1.97  fof(f40,plain,(
% 11.54/1.97    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.54/1.97    inference(flattening,[],[f39])).
% 11.54/1.97  
% 11.54/1.97  fof(f95,plain,(
% 11.54/1.97    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.54/1.97    inference(cnf_transformation,[],[f40])).
% 11.54/1.97  
% 11.54/1.97  fof(f1,axiom,(
% 11.54/1.97    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.54/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.54/1.97  
% 11.54/1.97  fof(f43,plain,(
% 11.54/1.97    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.54/1.97    inference(nnf_transformation,[],[f1])).
% 11.54/1.97  
% 11.54/1.97  fof(f44,plain,(
% 11.54/1.97    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.54/1.97    inference(flattening,[],[f43])).
% 11.54/1.97  
% 11.54/1.97  fof(f61,plain,(
% 11.54/1.97    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.54/1.97    inference(cnf_transformation,[],[f44])).
% 11.54/1.97  
% 11.54/1.97  fof(f7,axiom,(
% 11.54/1.97    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 11.54/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.54/1.97  
% 11.54/1.97  fof(f52,plain,(
% 11.54/1.97    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 11.54/1.97    inference(nnf_transformation,[],[f7])).
% 11.54/1.97  
% 11.54/1.97  fof(f53,plain,(
% 11.54/1.97    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 11.54/1.97    inference(flattening,[],[f52])).
% 11.54/1.97  
% 11.54/1.97  fof(f75,plain,(
% 11.54/1.97    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 11.54/1.97    inference(cnf_transformation,[],[f53])).
% 11.54/1.97  
% 11.54/1.97  fof(f124,plain,(
% 11.54/1.97    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 11.54/1.97    inference(equality_resolution,[],[f75])).
% 11.54/1.97  
% 11.54/1.97  fof(f76,plain,(
% 11.54/1.97    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 11.54/1.97    inference(cnf_transformation,[],[f53])).
% 11.54/1.97  
% 11.54/1.97  fof(f123,plain,(
% 11.54/1.97    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 11.54/1.97    inference(equality_resolution,[],[f76])).
% 11.54/1.97  
% 11.54/1.97  fof(f92,plain,(
% 11.54/1.97    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.54/1.97    inference(cnf_transformation,[],[f37])).
% 11.54/1.97  
% 11.54/1.97  fof(f13,axiom,(
% 11.54/1.97    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 11.54/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.54/1.97  
% 11.54/1.97  fof(f30,plain,(
% 11.54/1.97    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.54/1.97    inference(ennf_transformation,[],[f13])).
% 11.54/1.97  
% 11.54/1.97  fof(f56,plain,(
% 11.54/1.97    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 11.54/1.97    inference(nnf_transformation,[],[f30])).
% 11.54/1.97  
% 11.54/1.97  fof(f84,plain,(
% 11.54/1.97    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.54/1.97    inference(cnf_transformation,[],[f56])).
% 11.54/1.97  
% 11.54/1.97  cnf(c_15,plain,
% 11.54/1.97      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 11.54/1.97      inference(cnf_transformation,[],[f77]) ).
% 11.54/1.97  
% 11.54/1.97  cnf(c_1508,plain,
% 11.54/1.97      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 11.54/1.97      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.54/1.97  
% 11.54/1.97  cnf(c_17,plain,
% 11.54/1.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 11.54/1.97      inference(cnf_transformation,[],[f78]) ).
% 11.54/1.97  
% 11.54/1.97  cnf(c_1506,plain,
% 11.54/1.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.54/1.97      | r1_tarski(X0,X1) = iProver_top ),
% 11.54/1.97      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.54/1.97  
% 11.54/1.97  cnf(c_2775,plain,
% 11.54/1.97      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 11.54/1.97      inference(superposition,[status(thm)],[c_1508,c_1506]) ).
% 11.54/1.97  
% 11.54/1.97  cnf(c_36,negated_conjecture,
% 11.54/1.97      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
% 11.54/1.97      inference(cnf_transformation,[],[f113]) ).
% 11.54/1.97  
% 11.54/1.97  cnf(c_1495,plain,
% 11.54/1.97      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) = iProver_top ),
% 11.54/1.97      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 11.54/1.97  
% 11.54/1.97  cnf(c_30,plain,
% 11.54/1.97      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 11.54/1.97      inference(cnf_transformation,[],[f91]) ).
% 11.54/1.97  
% 11.54/1.97  cnf(c_1498,plain,
% 11.54/1.97      ( v4_relat_1(X0,X1) = iProver_top
% 11.54/1.97      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 11.54/1.97      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_3644,plain,
% 11.54/1.98      ( v4_relat_1(sK4,k2_enumset1(sK1,sK1,sK1,sK1)) = iProver_top ),
% 11.54/1.98      inference(superposition,[status(thm)],[c_1495,c_1498]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_21,plain,
% 11.54/1.98      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 11.54/1.98      inference(cnf_transformation,[],[f82]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_1503,plain,
% 11.54/1.98      ( v4_relat_1(X0,X1) != iProver_top
% 11.54/1.98      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 11.54/1.98      | v1_relat_1(X0) != iProver_top ),
% 11.54/1.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_11,plain,
% 11.54/1.98      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
% 11.54/1.98      | k2_enumset1(X1,X1,X1,X1) = X0
% 11.54/1.98      | k1_xboole_0 = X0 ),
% 11.54/1.98      inference(cnf_transformation,[],[f110]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_1509,plain,
% 11.54/1.98      ( k2_enumset1(X0,X0,X0,X0) = X1
% 11.54/1.98      | k1_xboole_0 = X1
% 11.54/1.98      | r1_tarski(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
% 11.54/1.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_6094,plain,
% 11.54/1.98      ( k2_enumset1(X0,X0,X0,X0) = k1_relat_1(X1)
% 11.54/1.98      | k1_relat_1(X1) = k1_xboole_0
% 11.54/1.98      | v4_relat_1(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top
% 11.54/1.98      | v1_relat_1(X1) != iProver_top ),
% 11.54/1.98      inference(superposition,[status(thm)],[c_1503,c_1509]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_15008,plain,
% 11.54/1.98      ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK4)
% 11.54/1.98      | k1_relat_1(sK4) = k1_xboole_0
% 11.54/1.98      | v1_relat_1(sK4) != iProver_top ),
% 11.54/1.98      inference(superposition,[status(thm)],[c_3644,c_6094]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_24,plain,
% 11.54/1.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 11.54/1.98      inference(cnf_transformation,[],[f86]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_1502,plain,
% 11.54/1.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 11.54/1.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_2776,plain,
% 11.54/1.98      ( r1_tarski(sK4,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) = iProver_top ),
% 11.54/1.98      inference(superposition,[status(thm)],[c_1495,c_1506]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_19,plain,
% 11.54/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 11.54/1.98      inference(cnf_transformation,[],[f81]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_16,plain,
% 11.54/1.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.54/1.98      inference(cnf_transformation,[],[f79]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_269,plain,
% 11.54/1.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 11.54/1.98      inference(prop_impl,[status(thm)],[c_16]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_270,plain,
% 11.54/1.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.54/1.98      inference(renaming,[status(thm)],[c_269]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_332,plain,
% 11.54/1.98      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 11.54/1.98      inference(bin_hyper_res,[status(thm)],[c_19,c_270]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_1494,plain,
% 11.54/1.98      ( r1_tarski(X0,X1) != iProver_top
% 11.54/1.98      | v1_relat_1(X1) != iProver_top
% 11.54/1.98      | v1_relat_1(X0) = iProver_top ),
% 11.54/1.98      inference(predicate_to_equality,[status(thm)],[c_332]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_2900,plain,
% 11.54/1.98      ( v1_relat_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != iProver_top
% 11.54/1.98      | v1_relat_1(sK4) = iProver_top ),
% 11.54/1.98      inference(superposition,[status(thm)],[c_2776,c_1494]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_3136,plain,
% 11.54/1.98      ( v1_relat_1(sK4) = iProver_top ),
% 11.54/1.98      inference(superposition,[status(thm)],[c_1502,c_2900]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_15240,plain,
% 11.54/1.98      ( k1_relat_1(sK4) = k1_xboole_0
% 11.54/1.98      | k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK4) ),
% 11.54/1.98      inference(global_propositional_subsumption,
% 11.54/1.98                [status(thm)],
% 11.54/1.98                [c_15008,c_3136]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_15241,plain,
% 11.54/1.98      ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK4)
% 11.54/1.98      | k1_relat_1(sK4) = k1_xboole_0 ),
% 11.54/1.98      inference(renaming,[status(thm)],[c_15240]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_15249,plain,
% 11.54/1.98      ( k2_enumset1(sK1,sK1,sK1,sK1) = X0
% 11.54/1.98      | k1_relat_1(sK4) = k1_xboole_0
% 11.54/1.98      | k1_xboole_0 = X0
% 11.54/1.98      | r1_tarski(X0,k1_relat_1(sK4)) != iProver_top ),
% 11.54/1.98      inference(superposition,[status(thm)],[c_15241,c_1509]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_34,negated_conjecture,
% 11.54/1.98      ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) ),
% 11.54/1.98      inference(cnf_transformation,[],[f112]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_40,plain,
% 11.54/1.98      ( r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
% 11.54/1.98      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_31,plain,
% 11.54/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.54/1.98      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 11.54/1.98      inference(cnf_transformation,[],[f93]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_1736,plain,
% 11.54/1.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))
% 11.54/1.98      | k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3) = k9_relat_1(sK4,sK3) ),
% 11.54/1.98      inference(instantiation,[status(thm)],[c_31]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_855,plain,
% 11.54/1.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.54/1.98      theory(equality) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_1555,plain,
% 11.54/1.98      ( ~ r1_tarski(X0,X1)
% 11.54/1.98      | r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)))
% 11.54/1.98      | k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3) != X0
% 11.54/1.98      | k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) != X1 ),
% 11.54/1.98      inference(instantiation,[status(thm)],[c_855]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_1650,plain,
% 11.54/1.98      ( r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)))
% 11.54/1.98      | ~ r1_tarski(k9_relat_1(sK4,sK3),X0)
% 11.54/1.98      | k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3) != k9_relat_1(sK4,sK3)
% 11.54/1.98      | k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) != X0 ),
% 11.54/1.98      inference(instantiation,[status(thm)],[c_1555]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_1987,plain,
% 11.54/1.98      ( r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)))
% 11.54/1.98      | ~ r1_tarski(k9_relat_1(sK4,sK3),k2_relat_1(sK4))
% 11.54/1.98      | k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3) != k9_relat_1(sK4,sK3)
% 11.54/1.98      | k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) != k2_relat_1(sK4) ),
% 11.54/1.98      inference(instantiation,[status(thm)],[c_1650]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_1988,plain,
% 11.54/1.98      ( k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3) != k9_relat_1(sK4,sK3)
% 11.54/1.98      | k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) != k2_relat_1(sK4)
% 11.54/1.98      | r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) = iProver_top
% 11.54/1.98      | r1_tarski(k9_relat_1(sK4,sK3),k2_relat_1(sK4)) != iProver_top ),
% 11.54/1.98      inference(predicate_to_equality,[status(thm)],[c_1987]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_25,plain,
% 11.54/1.98      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 11.54/1.98      inference(cnf_transformation,[],[f87]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_2395,plain,
% 11.54/1.98      ( r1_tarski(k9_relat_1(sK4,sK3),k2_relat_1(sK4)) | ~ v1_relat_1(sK4) ),
% 11.54/1.98      inference(instantiation,[status(thm)],[c_25]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_2396,plain,
% 11.54/1.98      ( r1_tarski(k9_relat_1(sK4,sK3),k2_relat_1(sK4)) = iProver_top
% 11.54/1.98      | v1_relat_1(sK4) != iProver_top ),
% 11.54/1.98      inference(predicate_to_equality,[status(thm)],[c_2395]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_6,plain,
% 11.54/1.98      ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) ),
% 11.54/1.98      inference(cnf_transformation,[],[f117]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_1514,plain,
% 11.54/1.98      ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) = iProver_top ),
% 11.54/1.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_15245,plain,
% 11.54/1.98      ( k1_relat_1(sK4) = k1_xboole_0
% 11.54/1.98      | r2_hidden(sK1,k1_relat_1(sK4)) = iProver_top ),
% 11.54/1.98      inference(superposition,[status(thm)],[c_15241,c_1514]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_28,plain,
% 11.54/1.98      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 11.54/1.98      | ~ r2_hidden(X2,k1_relat_1(X1))
% 11.54/1.98      | ~ v1_funct_1(X1)
% 11.54/1.98      | ~ v1_relat_1(X1)
% 11.54/1.98      | k2_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X0)) = k9_relat_1(X1,k2_enumset1(X2,X2,X2,X0)) ),
% 11.54/1.98      inference(cnf_transformation,[],[f111]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_37,negated_conjecture,
% 11.54/1.98      ( v1_funct_1(sK4) ),
% 11.54/1.98      inference(cnf_transformation,[],[f96]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_444,plain,
% 11.54/1.98      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 11.54/1.98      | ~ r2_hidden(X2,k1_relat_1(X1))
% 11.54/1.98      | ~ v1_relat_1(X1)
% 11.54/1.98      | k2_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X0)) = k9_relat_1(X1,k2_enumset1(X2,X2,X2,X0))
% 11.54/1.98      | sK4 != X1 ),
% 11.54/1.98      inference(resolution_lifted,[status(thm)],[c_28,c_37]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_445,plain,
% 11.54/1.98      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 11.54/1.98      | ~ r2_hidden(X1,k1_relat_1(sK4))
% 11.54/1.98      | ~ v1_relat_1(sK4)
% 11.54/1.98      | k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X1)) = k9_relat_1(sK4,k2_enumset1(X0,X0,X0,X1)) ),
% 11.54/1.98      inference(unflattening,[status(thm)],[c_444]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_1493,plain,
% 11.54/1.98      ( k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X1)) = k9_relat_1(sK4,k2_enumset1(X0,X0,X0,X1))
% 11.54/1.98      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 11.54/1.98      | r2_hidden(X1,k1_relat_1(sK4)) != iProver_top
% 11.54/1.98      | v1_relat_1(sK4) != iProver_top ),
% 11.54/1.98      inference(predicate_to_equality,[status(thm)],[c_445]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_16452,plain,
% 11.54/1.98      ( k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,X0)) = k9_relat_1(sK4,k2_enumset1(sK1,sK1,sK1,X0))
% 11.54/1.98      | k1_relat_1(sK4) = k1_xboole_0
% 11.54/1.98      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 11.54/1.98      | v1_relat_1(sK4) != iProver_top ),
% 11.54/1.98      inference(superposition,[status(thm)],[c_15245,c_1493]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_16950,plain,
% 11.54/1.98      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 11.54/1.98      | k1_relat_1(sK4) = k1_xboole_0
% 11.54/1.98      | k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,X0)) = k9_relat_1(sK4,k2_enumset1(sK1,sK1,sK1,X0)) ),
% 11.54/1.98      inference(global_propositional_subsumption,
% 11.54/1.98                [status(thm)],
% 11.54/1.98                [c_16452,c_3136]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_16951,plain,
% 11.54/1.98      ( k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,X0)) = k9_relat_1(sK4,k2_enumset1(sK1,sK1,sK1,X0))
% 11.54/1.98      | k1_relat_1(sK4) = k1_xboole_0
% 11.54/1.98      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
% 11.54/1.98      inference(renaming,[status(thm)],[c_16950]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_16958,plain,
% 11.54/1.98      ( k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) = k9_relat_1(sK4,k2_enumset1(sK1,sK1,sK1,sK1))
% 11.54/1.98      | k1_relat_1(sK4) = k1_xboole_0 ),
% 11.54/1.98      inference(superposition,[status(thm)],[c_15245,c_16951]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_27,plain,
% 11.54/1.98      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 11.54/1.98      inference(cnf_transformation,[],[f89]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_1499,plain,
% 11.54/1.98      ( k7_relat_1(X0,X1) = X0
% 11.54/1.98      | v4_relat_1(X0,X1) != iProver_top
% 11.54/1.98      | v1_relat_1(X0) != iProver_top ),
% 11.54/1.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_5041,plain,
% 11.54/1.98      ( k7_relat_1(sK4,k2_enumset1(sK1,sK1,sK1,sK1)) = sK4
% 11.54/1.98      | v1_relat_1(sK4) != iProver_top ),
% 11.54/1.98      inference(superposition,[status(thm)],[c_3644,c_1499]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_5181,plain,
% 11.54/1.98      ( k7_relat_1(sK4,k2_enumset1(sK1,sK1,sK1,sK1)) = sK4 ),
% 11.54/1.98      inference(global_propositional_subsumption,[status(thm)],[c_5041,c_3136]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_26,plain,
% 11.54/1.98      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 11.54/1.98      inference(cnf_transformation,[],[f88]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_1500,plain,
% 11.54/1.98      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 11.54/1.98      | v1_relat_1(X0) != iProver_top ),
% 11.54/1.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_3383,plain,
% 11.54/1.98      ( k2_relat_1(k7_relat_1(sK4,X0)) = k9_relat_1(sK4,X0) ),
% 11.54/1.98      inference(superposition,[status(thm)],[c_3136,c_1500]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_5186,plain,
% 11.54/1.98      ( k9_relat_1(sK4,k2_enumset1(sK1,sK1,sK1,sK1)) = k2_relat_1(sK4) ),
% 11.54/1.98      inference(superposition,[status(thm)],[c_5181,c_3383]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_16960,plain,
% 11.54/1.98      ( k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) = k2_relat_1(sK4)
% 11.54/1.98      | k1_relat_1(sK4) = k1_xboole_0 ),
% 11.54/1.98      inference(light_normalisation,[status(thm)],[c_16958,c_5186]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_17818,plain,
% 11.54/1.98      ( k1_relat_1(sK4) = k1_xboole_0 ),
% 11.54/1.98      inference(global_propositional_subsumption,
% 11.54/1.98                [status(thm)],
% 11.54/1.98                [c_15249,c_36,c_40,c_1736,c_1988,c_2396,c_3136,c_16960]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_32,plain,
% 11.54/1.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 11.54/1.98      | ~ v1_funct_1(X0)
% 11.54/1.98      | ~ v1_relat_1(X0) ),
% 11.54/1.98      inference(cnf_transformation,[],[f95]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_462,plain,
% 11.54/1.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 11.54/1.98      | ~ v1_relat_1(X0)
% 11.54/1.98      | sK4 != X0 ),
% 11.54/1.98      inference(resolution_lifted,[status(thm)],[c_32,c_37]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_463,plain,
% 11.54/1.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4))))
% 11.54/1.98      | ~ v1_relat_1(sK4) ),
% 11.54/1.98      inference(unflattening,[status(thm)],[c_462]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_1492,plain,
% 11.54/1.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4)))) = iProver_top
% 11.54/1.98      | v1_relat_1(sK4) != iProver_top ),
% 11.54/1.98      inference(predicate_to_equality,[status(thm)],[c_463]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_2777,plain,
% 11.54/1.98      ( r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4))) = iProver_top
% 11.54/1.98      | v1_relat_1(sK4) != iProver_top ),
% 11.54/1.98      inference(superposition,[status(thm)],[c_1492,c_1506]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_0,plain,
% 11.54/1.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 11.54/1.98      inference(cnf_transformation,[],[f61]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_1519,plain,
% 11.54/1.98      ( X0 = X1
% 11.54/1.98      | r1_tarski(X0,X1) != iProver_top
% 11.54/1.98      | r1_tarski(X1,X0) != iProver_top ),
% 11.54/1.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_3778,plain,
% 11.54/1.98      ( k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4)) = sK4
% 11.54/1.98      | r1_tarski(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4)),sK4) != iProver_top
% 11.54/1.98      | v1_relat_1(sK4) != iProver_top ),
% 11.54/1.98      inference(superposition,[status(thm)],[c_2777,c_1519]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_4646,plain,
% 11.54/1.98      ( r1_tarski(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4)),sK4) != iProver_top
% 11.54/1.98      | k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4)) = sK4 ),
% 11.54/1.98      inference(global_propositional_subsumption,[status(thm)],[c_3778,c_3136]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_4647,plain,
% 11.54/1.98      ( k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4)) = sK4
% 11.54/1.98      | r1_tarski(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4)),sK4) != iProver_top ),
% 11.54/1.98      inference(renaming,[status(thm)],[c_4646]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_17890,plain,
% 11.54/1.98      ( k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4)) = sK4
% 11.54/1.98      | r1_tarski(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4)),sK4) != iProver_top ),
% 11.54/1.98      inference(demodulation,[status(thm)],[c_17818,c_4647]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_13,plain,
% 11.54/1.98      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 11.54/1.98      inference(cnf_transformation,[],[f124]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_17898,plain,
% 11.54/1.98      ( sK4 = k1_xboole_0 | r1_tarski(k1_xboole_0,sK4) != iProver_top ),
% 11.54/1.98      inference(demodulation,[status(thm)],[c_17890,c_13]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_18054,plain,
% 11.54/1.98      ( sK4 = k1_xboole_0 ),
% 11.54/1.98      inference(superposition,[status(thm)],[c_2775,c_17898]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_1497,plain,
% 11.54/1.98      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 11.54/1.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.54/1.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_3536,plain,
% 11.54/1.98      ( k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,X0) = k9_relat_1(sK4,X0) ),
% 11.54/1.98      inference(superposition,[status(thm)],[c_1495,c_1497]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_1496,plain,
% 11.54/1.98      ( r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
% 11.54/1.98      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_3968,plain,
% 11.54/1.98      ( r1_tarski(k9_relat_1(sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
% 11.54/1.98      inference(demodulation,[status(thm)],[c_3536,c_1496]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_18960,plain,
% 11.54/1.98      ( r1_tarski(k9_relat_1(k1_xboole_0,sK3),k2_enumset1(k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1))) != iProver_top ),
% 11.54/1.98      inference(demodulation,[status(thm)],[c_18054,c_3968]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_3642,plain,
% 11.54/1.98      ( v4_relat_1(k1_xboole_0,X0) = iProver_top ),
% 11.54/1.98      inference(superposition,[status(thm)],[c_1508,c_1498]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_6567,plain,
% 11.54/1.98      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
% 11.54/1.98      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 11.54/1.98      inference(superposition,[status(thm)],[c_3642,c_1499]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_12,plain,
% 11.54/1.98      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 11.54/1.98      inference(cnf_transformation,[],[f123]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_2209,plain,
% 11.54/1.98      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 11.54/1.98      inference(superposition,[status(thm)],[c_12,c_1502]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_2211,plain,
% 11.54/1.98      ( v1_relat_1(k1_xboole_0) ),
% 11.54/1.98      inference(predicate_to_equality_rev,[status(thm)],[c_2209]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_3648,plain,
% 11.54/1.98      ( v4_relat_1(k1_xboole_0,X0) ),
% 11.54/1.98      inference(predicate_to_equality_rev,[status(thm)],[c_3642]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_3667,plain,
% 11.54/1.98      ( ~ v4_relat_1(k1_xboole_0,X0)
% 11.54/1.98      | ~ v1_relat_1(k1_xboole_0)
% 11.54/1.98      | k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 11.54/1.98      inference(instantiation,[status(thm)],[c_27]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_7742,plain,
% 11.54/1.98      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 11.54/1.98      inference(global_propositional_subsumption,
% 11.54/1.98                [status(thm)],
% 11.54/1.98                [c_6567,c_2211,c_3648,c_3667]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_3017,plain,
% 11.54/1.98      ( k2_relat_1(k7_relat_1(k1_xboole_0,X0)) = k9_relat_1(k1_xboole_0,X0) ),
% 11.54/1.98      inference(superposition,[status(thm)],[c_2209,c_1500]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_7745,plain,
% 11.54/1.98      ( k9_relat_1(k1_xboole_0,X0) = k2_relat_1(k1_xboole_0) ),
% 11.54/1.98      inference(demodulation,[status(thm)],[c_7742,c_3017]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_29,plain,
% 11.54/1.98      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 11.54/1.98      inference(cnf_transformation,[],[f92]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_23,plain,
% 11.54/1.98      ( ~ v5_relat_1(X0,X1) | r1_tarski(k2_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 11.54/1.98      inference(cnf_transformation,[],[f84]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_480,plain,
% 11.54/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.54/1.98      | r1_tarski(k2_relat_1(X0),X2)
% 11.54/1.98      | ~ v1_relat_1(X0) ),
% 11.54/1.98      inference(resolution,[status(thm)],[c_29,c_23]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_1491,plain,
% 11.54/1.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.54/1.98      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 11.54/1.98      | v1_relat_1(X0) != iProver_top ),
% 11.54/1.98      inference(predicate_to_equality,[status(thm)],[c_480]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_2275,plain,
% 11.54/1.98      ( r1_tarski(k2_relat_1(k1_xboole_0),X0) = iProver_top
% 11.54/1.98      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 11.54/1.98      inference(superposition,[status(thm)],[c_1508,c_1491]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_2627,plain,
% 11.54/1.98      ( r1_tarski(k2_relat_1(k1_xboole_0),X0) = iProver_top ),
% 11.54/1.98      inference(global_propositional_subsumption,[status(thm)],[c_2275,c_2209]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_6400,plain,
% 11.54/1.98      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 11.54/1.98      inference(superposition,[status(thm)],[c_2775,c_1519]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_7193,plain,
% 11.54/1.98      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 11.54/1.98      inference(superposition,[status(thm)],[c_2627,c_6400]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_7746,plain,
% 11.54/1.98      ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 11.54/1.98      inference(light_normalisation,[status(thm)],[c_7745,c_7193]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_18981,plain,
% 11.54/1.98      ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1))) != iProver_top ),
% 11.54/1.98      inference(demodulation,[status(thm)],[c_18960,c_7746]) ).
% 11.54/1.98  
% 11.54/1.98  cnf(c_23239,plain,
% 11.54/1.98      ( $false ),
% 11.54/1.98      inference(superposition,[status(thm)],[c_2775,c_18981]) ).
% 11.54/1.98  
% 11.54/1.98  
% 11.54/1.98  % SZS output end CNFRefutation for theBenchmark.p
% 11.54/1.98  
% 11.54/1.98  ------                               Statistics
% 11.54/1.98  
% 11.54/1.98  ------ General
% 11.54/1.98  
% 11.54/1.98  abstr_ref_over_cycles:                  0
% 11.54/1.98  abstr_ref_under_cycles:                 0
% 11.54/1.98  gc_basic_clause_elim:                   0
% 11.54/1.98  forced_gc_time:                         0
% 11.54/1.98  parsing_time:                           0.009
% 11.54/1.98  unif_index_cands_time:                  0.
% 11.54/1.98  unif_index_add_time:                    0.
% 11.54/1.98  orderings_time:                         0.
% 11.54/1.98  out_proof_time:                         0.012
% 11.54/1.98  total_time:                             1.308
% 11.54/1.98  num_of_symbols:                         53
% 11.54/1.98  num_of_terms:                           35404
% 11.54/1.98  
% 11.54/1.98  ------ Preprocessing
% 11.54/1.98  
% 11.54/1.98  num_of_splits:                          0
% 11.54/1.98  num_of_split_atoms:                     0
% 11.54/1.98  num_of_reused_defs:                     0
% 11.54/1.98  num_eq_ax_congr_red:                    25
% 11.54/1.98  num_of_sem_filtered_clauses:            1
% 11.54/1.98  num_of_subtypes:                        0
% 11.54/1.98  monotx_restored_types:                  0
% 11.54/1.98  sat_num_of_epr_types:                   0
% 11.54/1.98  sat_num_of_non_cyclic_types:            0
% 11.54/1.98  sat_guarded_non_collapsed_types:        0
% 11.54/1.98  num_pure_diseq_elim:                    0
% 11.54/1.98  simp_replaced_by:                       0
% 11.54/1.98  res_preprocessed:                       164
% 11.54/1.98  prep_upred:                             0
% 11.54/1.98  prep_unflattend:                        2
% 11.54/1.98  smt_new_axioms:                         0
% 11.54/1.98  pred_elim_cands:                        5
% 11.54/1.98  pred_elim:                              2
% 11.54/1.98  pred_elim_cl:                           3
% 11.54/1.98  pred_elim_cycles:                       4
% 11.54/1.98  merged_defs:                            8
% 11.54/1.98  merged_defs_ncl:                        0
% 11.54/1.98  bin_hyper_res:                          9
% 11.54/1.98  prep_cycles:                            4
% 11.54/1.98  pred_elim_time:                         0.004
% 11.54/1.98  splitting_time:                         0.
% 11.54/1.98  sem_filter_time:                        0.
% 11.54/1.98  monotx_time:                            0.
% 11.54/1.98  subtype_inf_time:                       0.
% 11.54/1.98  
% 11.54/1.98  ------ Problem properties
% 11.54/1.98  
% 11.54/1.98  clauses:                                33
% 11.54/1.98  conjectures:                            3
% 11.54/1.98  epr:                                    4
% 11.54/1.98  horn:                                   29
% 11.54/1.98  ground:                                 4
% 11.54/1.98  unary:                                  12
% 11.54/1.98  binary:                                 7
% 11.54/1.98  lits:                                   70
% 11.54/1.98  lits_eq:                                22
% 11.54/1.98  fd_pure:                                0
% 11.54/1.98  fd_pseudo:                              0
% 11.54/1.98  fd_cond:                                1
% 11.54/1.98  fd_pseudo_cond:                         5
% 11.54/1.98  ac_symbols:                             0
% 11.54/1.98  
% 11.54/1.98  ------ Propositional Solver
% 11.54/1.98  
% 11.54/1.98  prop_solver_calls:                      29
% 11.54/1.98  prop_fast_solver_calls:                 3137
% 11.54/1.98  smt_solver_calls:                       0
% 11.54/1.98  smt_fast_solver_calls:                  0
% 11.54/1.98  prop_num_of_clauses:                    11283
% 11.54/1.98  prop_preprocess_simplified:             18853
% 11.54/1.98  prop_fo_subsumed:                       85
% 11.54/1.98  prop_solver_time:                       0.
% 11.54/1.98  smt_solver_time:                        0.
% 11.54/1.98  smt_fast_solver_time:                   0.
% 11.54/1.98  prop_fast_solver_time:                  0.
% 11.54/1.98  prop_unsat_core_time:                   0.
% 11.54/1.98  
% 11.54/1.98  ------ QBF
% 11.54/1.98  
% 11.54/1.98  qbf_q_res:                              0
% 11.54/1.98  qbf_num_tautologies:                    0
% 11.54/1.98  qbf_prep_cycles:                        0
% 11.54/1.98  
% 11.54/1.98  ------ BMC1
% 11.54/1.98  
% 11.54/1.98  bmc1_current_bound:                     -1
% 11.54/1.98  bmc1_last_solved_bound:                 -1
% 11.54/1.98  bmc1_unsat_core_size:                   -1
% 11.54/1.98  bmc1_unsat_core_parents_size:           -1
% 11.54/1.98  bmc1_merge_next_fun:                    0
% 11.54/1.98  bmc1_unsat_core_clauses_time:           0.
% 11.54/1.98  
% 11.54/1.98  ------ Instantiation
% 11.54/1.98  
% 11.54/1.98  inst_num_of_clauses:                    2311
% 11.54/1.98  inst_num_in_passive:                    202
% 11.54/1.98  inst_num_in_active:                     1024
% 11.54/1.98  inst_num_in_unprocessed:                1085
% 11.54/1.98  inst_num_of_loops:                      1160
% 11.54/1.98  inst_num_of_learning_restarts:          0
% 11.54/1.98  inst_num_moves_active_passive:          136
% 11.54/1.98  inst_lit_activity:                      0
% 11.54/1.98  inst_lit_activity_moves:                0
% 11.54/1.98  inst_num_tautologies:                   0
% 11.54/1.98  inst_num_prop_implied:                  0
% 11.54/1.98  inst_num_existing_simplified:           0
% 11.54/1.98  inst_num_eq_res_simplified:             0
% 11.54/1.98  inst_num_child_elim:                    0
% 11.54/1.98  inst_num_of_dismatching_blockings:      2008
% 11.54/1.98  inst_num_of_non_proper_insts:           2947
% 11.54/1.98  inst_num_of_duplicates:                 0
% 11.54/1.98  inst_inst_num_from_inst_to_res:         0
% 11.54/1.98  inst_dismatching_checking_time:         0.
% 11.54/1.98  
% 11.54/1.98  ------ Resolution
% 11.54/1.98  
% 11.54/1.98  res_num_of_clauses:                     0
% 11.54/1.98  res_num_in_passive:                     0
% 11.54/1.98  res_num_in_active:                      0
% 11.54/1.98  res_num_of_loops:                       168
% 11.54/1.98  res_forward_subset_subsumed:            529
% 11.54/1.98  res_backward_subset_subsumed:           0
% 11.54/1.98  res_forward_subsumed:                   0
% 11.54/1.98  res_backward_subsumed:                  0
% 11.54/1.98  res_forward_subsumption_resolution:     0
% 11.54/1.98  res_backward_subsumption_resolution:    0
% 11.54/1.98  res_clause_to_clause_subsumption:       20137
% 11.54/1.98  res_orphan_elimination:                 0
% 11.54/1.98  res_tautology_del:                      141
% 11.54/1.98  res_num_eq_res_simplified:              0
% 11.54/1.98  res_num_sel_changes:                    0
% 11.54/1.98  res_moves_from_active_to_pass:          0
% 11.54/1.98  
% 11.54/1.98  ------ Superposition
% 11.54/1.98  
% 11.54/1.98  sup_time_total:                         0.
% 11.54/1.98  sup_time_generating:                    0.
% 11.54/1.98  sup_time_sim_full:                      0.
% 11.54/1.98  sup_time_sim_immed:                     0.
% 11.54/1.98  
% 11.54/1.98  sup_num_of_clauses:                     1557
% 11.54/1.98  sup_num_in_active:                      105
% 11.54/1.98  sup_num_in_passive:                     1452
% 11.54/1.98  sup_num_of_loops:                       231
% 11.54/1.98  sup_fw_superposition:                   1186
% 11.54/1.98  sup_bw_superposition:                   1131
% 11.54/1.98  sup_immediate_simplified:               572
% 11.54/1.98  sup_given_eliminated:                   2
% 11.54/1.98  comparisons_done:                       0
% 11.54/1.98  comparisons_avoided:                    3745
% 11.54/1.98  
% 11.54/1.98  ------ Simplifications
% 11.54/1.98  
% 11.54/1.98  
% 11.54/1.98  sim_fw_subset_subsumed:                 90
% 11.54/1.98  sim_bw_subset_subsumed:                 18
% 11.54/1.98  sim_fw_subsumed:                        266
% 11.54/1.98  sim_bw_subsumed:                        52
% 11.54/1.98  sim_fw_subsumption_res:                 0
% 11.54/1.98  sim_bw_subsumption_res:                 0
% 11.54/1.98  sim_tautology_del:                      17
% 11.54/1.98  sim_eq_tautology_del:                   141
% 11.54/1.98  sim_eq_res_simp:                        12
% 11.54/1.98  sim_fw_demodulated:                     184
% 11.54/1.98  sim_bw_demodulated:                     114
% 11.54/1.98  sim_light_normalised:                   289
% 11.54/1.98  sim_joinable_taut:                      0
% 11.54/1.98  sim_joinable_simp:                      0
% 11.54/1.98  sim_ac_normalised:                      0
% 11.54/1.98  sim_smt_subsumption:                    0
% 11.54/1.98  
%------------------------------------------------------------------------------
