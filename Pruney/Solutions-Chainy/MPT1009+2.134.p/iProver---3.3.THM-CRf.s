%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:55 EST 2020

% Result     : Theorem 3.24s
% Output     : CNFRefutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :  181 (1043 expanded)
%              Number of clauses        :   96 ( 284 expanded)
%              Number of leaves         :   26 ( 238 expanded)
%              Depth                    :   22
%              Number of atoms          :  470 (2459 expanded)
%              Number of equality atoms :  277 (1122 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f53,plain,
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

fof(f54,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1)))
    & k1_xboole_0 != sK2
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f42,f53])).

fof(f89,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) ),
    inference(cnf_transformation,[],[f54])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f92,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f63,f64])).

fof(f93,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f62,f92])).

fof(f106,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
    inference(definition_unfolding,[],[f89,f93])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f48])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f102,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f65,f93,f93])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f13,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f16,axiom,(
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
    inference(ennf_transformation,[],[f16])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f91,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1))) ),
    inference(cnf_transformation,[],[f54])).

fof(f105,plain,(
    ~ r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) ),
    inference(definition_unfolding,[],[f91,f93,f93])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f78,plain,(
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

fof(f43,plain,(
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

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f44])).

fof(f46,plain,(
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

fof(f47,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f45,f46])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f98,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f57,f92])).

fof(f109,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f98])).

fof(f110,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_enumset1(X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f109])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f104,plain,(
    ! [X0,X1] :
      ( k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f85,f93])).

fof(f88,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f54])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f103,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f74,f93])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f36,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f83,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f50])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f114,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f70])).

fof(f17,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1847,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_28,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1850,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2813,plain,
    ( v4_relat_1(sK4,k2_enumset1(sK1,sK1,sK1,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1847,c_1850])).

cnf(c_18,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1857,plain,
    ( v4_relat_1(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1863,plain,
    ( k2_enumset1(X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4969,plain,
    ( k2_enumset1(X0,X0,X0,X0) = k1_relat_1(X1)
    | k1_relat_1(X1) = k1_xboole_0
    | v4_relat_1(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1857,c_1863])).

cnf(c_8021,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK4)
    | k1_relat_1(sK4) = k1_xboole_0
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2813,c_4969])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1860,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3900,plain,
    ( v1_relat_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1847,c_1860])).

cnf(c_19,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1856,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3909,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3900,c_1856])).

cnf(c_8485,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8021,c_3909])).

cnf(c_8486,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK4)
    | k1_relat_1(sK4) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_8485])).

cnf(c_22,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1853,plain,
    ( k7_relat_1(X0,X1) = X0
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3792,plain,
    ( k7_relat_1(sK4,k2_enumset1(sK1,sK1,sK1,sK1)) = sK4
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2813,c_1853])).

cnf(c_3999,plain,
    ( k7_relat_1(sK4,k2_enumset1(sK1,sK1,sK1,sK1)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3792,c_3909])).

cnf(c_8500,plain,
    ( k7_relat_1(sK4,k1_relat_1(sK4)) = sK4
    | k1_relat_1(sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8486,c_3999])).

cnf(c_30,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_36,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2169,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))
    | k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,X0) = k9_relat_1(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_2237,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))
    | k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3) = k9_relat_1(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_2169])).

cnf(c_20,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2594,plain,
    ( r1_tarski(k9_relat_1(sK4,sK3),k2_relat_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_2596,plain,
    ( r1_tarski(k9_relat_1(sK4,sK3),k2_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2594])).

cnf(c_1378,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2141,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)))
    | k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3) != X0
    | k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) != X1 ),
    inference(instantiation,[status(thm)],[c_1378])).

cnf(c_2236,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)))
    | ~ r1_tarski(k9_relat_1(sK4,sK3),X0)
    | k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3) != k9_relat_1(sK4,sK3)
    | k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) != X0 ),
    inference(instantiation,[status(thm)],[c_2141])).

cnf(c_2595,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)))
    | ~ r1_tarski(k9_relat_1(sK4,sK3),k2_relat_1(sK4))
    | k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3) != k9_relat_1(sK4,sK3)
    | k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) != k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2236])).

cnf(c_2598,plain,
    ( k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3) != k9_relat_1(sK4,sK3)
    | k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) != k2_relat_1(sK4)
    | r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) = iProver_top
    | r1_tarski(k9_relat_1(sK4,sK3),k2_relat_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2595])).

cnf(c_5,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1867,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_8489,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | r2_hidden(sK1,k1_relat_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8486,c_1867])).

cnf(c_27,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_325,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_33])).

cnf(c_326,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_325])).

cnf(c_1846,plain,
    ( k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0)
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_326])).

cnf(c_9064,plain,
    ( k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) = k11_relat_1(sK4,sK1)
    | k1_relat_1(sK4) = k1_xboole_0
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_8489,c_1846])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1859,plain,
    ( k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3911,plain,
    ( k9_relat_1(sK4,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_3909,c_1859])).

cnf(c_21,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1854,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3912,plain,
    ( k2_relat_1(k7_relat_1(sK4,X0)) = k9_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_3909,c_1854])).

cnf(c_4003,plain,
    ( k9_relat_1(sK4,k2_enumset1(sK1,sK1,sK1,sK1)) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_3999,c_3912])).

cnf(c_4287,plain,
    ( k11_relat_1(sK4,sK1) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_3911,c_4003])).

cnf(c_9065,plain,
    ( k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) = k2_relat_1(sK4)
    | k1_relat_1(sK4) = k1_xboole_0
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9064,c_4287])).

cnf(c_9067,plain,
    ( k1_relat_1(sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8500,c_32,c_36,c_2237,c_2596,c_2598,c_3909,c_9065])).

cnf(c_26,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1851,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_9257,plain,
    ( sK4 = k1_xboole_0
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_9067,c_1851])).

cnf(c_2270,plain,
    ( ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) != k1_xboole_0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_2276,plain,
    ( k1_relat_1(sK4) != k1_xboole_0
    | k1_xboole_0 = sK4
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2270])).

cnf(c_1376,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2285,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1376])).

cnf(c_1377,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2435,plain,
    ( X0 != X1
    | sK4 != X1
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_1377])).

cnf(c_3551,plain,
    ( X0 != sK4
    | sK4 = X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2435])).

cnf(c_3552,plain,
    ( sK4 != sK4
    | sK4 = k1_xboole_0
    | k1_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_3551])).

cnf(c_12977,plain,
    ( sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9257,c_32,c_36,c_2237,c_2276,c_2285,c_2596,c_2598,c_3552,c_3909,c_9065])).

cnf(c_1849,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_2182,plain,
    ( k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,X0) = k9_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_1847,c_1849])).

cnf(c_1848,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_2340,plain,
    ( r1_tarski(k9_relat_1(sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2182,c_1848])).

cnf(c_13008,plain,
    ( r1_tarski(k9_relat_1(k1_xboole_0,sK3),k2_enumset1(k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12977,c_2340])).

cnf(c_13,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1862,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2812,plain,
    ( v4_relat_1(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1862,c_1850])).

cnf(c_3791,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2812,c_1853])).

cnf(c_61,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_63,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_61])).

cnf(c_2072,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2073,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2072])).

cnf(c_2075,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2073])).

cnf(c_2099,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2102,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2099])).

cnf(c_2104,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2102])).

cnf(c_5652,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3791,c_63,c_2075,c_2104])).

cnf(c_10,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f114])).

cnf(c_2296,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_1856])).

cnf(c_2802,plain,
    ( k2_relat_1(k7_relat_1(k1_xboole_0,X0)) = k9_relat_1(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_2296,c_1854])).

cnf(c_5656,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_5652,c_2802])).

cnf(c_23,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_5657,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5656,c_23])).

cnf(c_13015,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13008,c_5657])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1872,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_14434,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_13015,c_1872])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:22:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.24/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.24/1.00  
% 3.24/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.24/1.00  
% 3.24/1.00  ------  iProver source info
% 3.24/1.00  
% 3.24/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.24/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.24/1.00  git: non_committed_changes: false
% 3.24/1.00  git: last_make_outside_of_git: false
% 3.24/1.00  
% 3.24/1.00  ------ 
% 3.24/1.00  
% 3.24/1.00  ------ Input Options
% 3.24/1.00  
% 3.24/1.00  --out_options                           all
% 3.24/1.00  --tptp_safe_out                         true
% 3.24/1.00  --problem_path                          ""
% 3.24/1.00  --include_path                          ""
% 3.24/1.00  --clausifier                            res/vclausify_rel
% 3.24/1.00  --clausifier_options                    --mode clausify
% 3.24/1.00  --stdin                                 false
% 3.24/1.00  --stats_out                             all
% 3.24/1.00  
% 3.24/1.00  ------ General Options
% 3.24/1.00  
% 3.24/1.00  --fof                                   false
% 3.24/1.00  --time_out_real                         305.
% 3.24/1.00  --time_out_virtual                      -1.
% 3.24/1.00  --symbol_type_check                     false
% 3.24/1.00  --clausify_out                          false
% 3.24/1.00  --sig_cnt_out                           false
% 3.24/1.00  --trig_cnt_out                          false
% 3.24/1.00  --trig_cnt_out_tolerance                1.
% 3.24/1.00  --trig_cnt_out_sk_spl                   false
% 3.24/1.00  --abstr_cl_out                          false
% 3.24/1.00  
% 3.24/1.00  ------ Global Options
% 3.24/1.00  
% 3.24/1.00  --schedule                              default
% 3.24/1.00  --add_important_lit                     false
% 3.24/1.00  --prop_solver_per_cl                    1000
% 3.24/1.00  --min_unsat_core                        false
% 3.24/1.00  --soft_assumptions                      false
% 3.24/1.00  --soft_lemma_size                       3
% 3.24/1.00  --prop_impl_unit_size                   0
% 3.24/1.00  --prop_impl_unit                        []
% 3.24/1.00  --share_sel_clauses                     true
% 3.24/1.00  --reset_solvers                         false
% 3.24/1.00  --bc_imp_inh                            [conj_cone]
% 3.24/1.00  --conj_cone_tolerance                   3.
% 3.24/1.00  --extra_neg_conj                        none
% 3.24/1.00  --large_theory_mode                     true
% 3.24/1.00  --prolific_symb_bound                   200
% 3.24/1.00  --lt_threshold                          2000
% 3.24/1.00  --clause_weak_htbl                      true
% 3.24/1.00  --gc_record_bc_elim                     false
% 3.24/1.00  
% 3.24/1.00  ------ Preprocessing Options
% 3.24/1.00  
% 3.24/1.00  --preprocessing_flag                    true
% 3.24/1.00  --time_out_prep_mult                    0.1
% 3.24/1.00  --splitting_mode                        input
% 3.24/1.00  --splitting_grd                         true
% 3.24/1.00  --splitting_cvd                         false
% 3.24/1.00  --splitting_cvd_svl                     false
% 3.24/1.00  --splitting_nvd                         32
% 3.24/1.00  --sub_typing                            true
% 3.24/1.00  --prep_gs_sim                           true
% 3.24/1.00  --prep_unflatten                        true
% 3.24/1.00  --prep_res_sim                          true
% 3.24/1.00  --prep_upred                            true
% 3.24/1.00  --prep_sem_filter                       exhaustive
% 3.24/1.00  --prep_sem_filter_out                   false
% 3.24/1.00  --pred_elim                             true
% 3.24/1.00  --res_sim_input                         true
% 3.24/1.00  --eq_ax_congr_red                       true
% 3.24/1.00  --pure_diseq_elim                       true
% 3.24/1.00  --brand_transform                       false
% 3.24/1.00  --non_eq_to_eq                          false
% 3.24/1.00  --prep_def_merge                        true
% 3.24/1.00  --prep_def_merge_prop_impl              false
% 3.24/1.00  --prep_def_merge_mbd                    true
% 3.24/1.00  --prep_def_merge_tr_red                 false
% 3.24/1.00  --prep_def_merge_tr_cl                  false
% 3.24/1.00  --smt_preprocessing                     true
% 3.24/1.00  --smt_ac_axioms                         fast
% 3.24/1.00  --preprocessed_out                      false
% 3.24/1.00  --preprocessed_stats                    false
% 3.24/1.00  
% 3.24/1.00  ------ Abstraction refinement Options
% 3.24/1.00  
% 3.24/1.00  --abstr_ref                             []
% 3.24/1.00  --abstr_ref_prep                        false
% 3.24/1.00  --abstr_ref_until_sat                   false
% 3.24/1.00  --abstr_ref_sig_restrict                funpre
% 3.24/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.24/1.00  --abstr_ref_under                       []
% 3.24/1.00  
% 3.24/1.00  ------ SAT Options
% 3.24/1.00  
% 3.24/1.00  --sat_mode                              false
% 3.24/1.00  --sat_fm_restart_options                ""
% 3.24/1.00  --sat_gr_def                            false
% 3.24/1.00  --sat_epr_types                         true
% 3.24/1.00  --sat_non_cyclic_types                  false
% 3.24/1.00  --sat_finite_models                     false
% 3.24/1.00  --sat_fm_lemmas                         false
% 3.24/1.00  --sat_fm_prep                           false
% 3.24/1.00  --sat_fm_uc_incr                        true
% 3.24/1.00  --sat_out_model                         small
% 3.24/1.00  --sat_out_clauses                       false
% 3.24/1.00  
% 3.24/1.00  ------ QBF Options
% 3.24/1.00  
% 3.24/1.00  --qbf_mode                              false
% 3.24/1.00  --qbf_elim_univ                         false
% 3.24/1.00  --qbf_dom_inst                          none
% 3.24/1.00  --qbf_dom_pre_inst                      false
% 3.24/1.00  --qbf_sk_in                             false
% 3.24/1.00  --qbf_pred_elim                         true
% 3.24/1.00  --qbf_split                             512
% 3.24/1.00  
% 3.24/1.00  ------ BMC1 Options
% 3.24/1.00  
% 3.24/1.00  --bmc1_incremental                      false
% 3.24/1.00  --bmc1_axioms                           reachable_all
% 3.24/1.00  --bmc1_min_bound                        0
% 3.24/1.00  --bmc1_max_bound                        -1
% 3.24/1.00  --bmc1_max_bound_default                -1
% 3.24/1.00  --bmc1_symbol_reachability              true
% 3.24/1.00  --bmc1_property_lemmas                  false
% 3.24/1.00  --bmc1_k_induction                      false
% 3.24/1.00  --bmc1_non_equiv_states                 false
% 3.24/1.00  --bmc1_deadlock                         false
% 3.24/1.00  --bmc1_ucm                              false
% 3.24/1.00  --bmc1_add_unsat_core                   none
% 3.24/1.00  --bmc1_unsat_core_children              false
% 3.24/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.24/1.00  --bmc1_out_stat                         full
% 3.24/1.00  --bmc1_ground_init                      false
% 3.24/1.00  --bmc1_pre_inst_next_state              false
% 3.24/1.00  --bmc1_pre_inst_state                   false
% 3.24/1.00  --bmc1_pre_inst_reach_state             false
% 3.24/1.00  --bmc1_out_unsat_core                   false
% 3.24/1.00  --bmc1_aig_witness_out                  false
% 3.24/1.00  --bmc1_verbose                          false
% 3.24/1.00  --bmc1_dump_clauses_tptp                false
% 3.24/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.24/1.00  --bmc1_dump_file                        -
% 3.24/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.24/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.24/1.00  --bmc1_ucm_extend_mode                  1
% 3.24/1.00  --bmc1_ucm_init_mode                    2
% 3.24/1.00  --bmc1_ucm_cone_mode                    none
% 3.24/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.24/1.00  --bmc1_ucm_relax_model                  4
% 3.24/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.24/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.24/1.00  --bmc1_ucm_layered_model                none
% 3.24/1.00  --bmc1_ucm_max_lemma_size               10
% 3.24/1.00  
% 3.24/1.00  ------ AIG Options
% 3.24/1.00  
% 3.24/1.00  --aig_mode                              false
% 3.24/1.00  
% 3.24/1.00  ------ Instantiation Options
% 3.24/1.00  
% 3.24/1.00  --instantiation_flag                    true
% 3.24/1.00  --inst_sos_flag                         false
% 3.24/1.00  --inst_sos_phase                        true
% 3.24/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.24/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.24/1.00  --inst_lit_sel_side                     num_symb
% 3.24/1.00  --inst_solver_per_active                1400
% 3.24/1.00  --inst_solver_calls_frac                1.
% 3.24/1.00  --inst_passive_queue_type               priority_queues
% 3.24/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.24/1.00  --inst_passive_queues_freq              [25;2]
% 3.24/1.00  --inst_dismatching                      true
% 3.24/1.00  --inst_eager_unprocessed_to_passive     true
% 3.24/1.00  --inst_prop_sim_given                   true
% 3.24/1.00  --inst_prop_sim_new                     false
% 3.24/1.00  --inst_subs_new                         false
% 3.24/1.00  --inst_eq_res_simp                      false
% 3.24/1.00  --inst_subs_given                       false
% 3.24/1.00  --inst_orphan_elimination               true
% 3.24/1.00  --inst_learning_loop_flag               true
% 3.24/1.00  --inst_learning_start                   3000
% 3.24/1.00  --inst_learning_factor                  2
% 3.24/1.00  --inst_start_prop_sim_after_learn       3
% 3.24/1.00  --inst_sel_renew                        solver
% 3.24/1.00  --inst_lit_activity_flag                true
% 3.24/1.00  --inst_restr_to_given                   false
% 3.24/1.00  --inst_activity_threshold               500
% 3.24/1.00  --inst_out_proof                        true
% 3.24/1.00  
% 3.24/1.00  ------ Resolution Options
% 3.24/1.00  
% 3.24/1.00  --resolution_flag                       true
% 3.24/1.00  --res_lit_sel                           adaptive
% 3.24/1.00  --res_lit_sel_side                      none
% 3.24/1.00  --res_ordering                          kbo
% 3.24/1.00  --res_to_prop_solver                    active
% 3.24/1.00  --res_prop_simpl_new                    false
% 3.24/1.00  --res_prop_simpl_given                  true
% 3.24/1.00  --res_passive_queue_type                priority_queues
% 3.24/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.24/1.00  --res_passive_queues_freq               [15;5]
% 3.24/1.00  --res_forward_subs                      full
% 3.24/1.00  --res_backward_subs                     full
% 3.24/1.00  --res_forward_subs_resolution           true
% 3.24/1.00  --res_backward_subs_resolution          true
% 3.24/1.00  --res_orphan_elimination                true
% 3.24/1.00  --res_time_limit                        2.
% 3.24/1.00  --res_out_proof                         true
% 3.24/1.00  
% 3.24/1.00  ------ Superposition Options
% 3.24/1.00  
% 3.24/1.00  --superposition_flag                    true
% 3.24/1.00  --sup_passive_queue_type                priority_queues
% 3.24/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.24/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.24/1.00  --demod_completeness_check              fast
% 3.24/1.00  --demod_use_ground                      true
% 3.24/1.00  --sup_to_prop_solver                    passive
% 3.24/1.00  --sup_prop_simpl_new                    true
% 3.24/1.00  --sup_prop_simpl_given                  true
% 3.24/1.00  --sup_fun_splitting                     false
% 3.24/1.00  --sup_smt_interval                      50000
% 3.24/1.00  
% 3.24/1.00  ------ Superposition Simplification Setup
% 3.24/1.00  
% 3.24/1.00  --sup_indices_passive                   []
% 3.24/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.24/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/1.00  --sup_full_bw                           [BwDemod]
% 3.24/1.00  --sup_immed_triv                        [TrivRules]
% 3.24/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.24/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/1.00  --sup_immed_bw_main                     []
% 3.24/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.24/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.24/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.24/1.00  
% 3.24/1.00  ------ Combination Options
% 3.24/1.00  
% 3.24/1.00  --comb_res_mult                         3
% 3.24/1.00  --comb_sup_mult                         2
% 3.24/1.00  --comb_inst_mult                        10
% 3.24/1.00  
% 3.24/1.00  ------ Debug Options
% 3.24/1.00  
% 3.24/1.00  --dbg_backtrace                         false
% 3.24/1.00  --dbg_dump_prop_clauses                 false
% 3.24/1.00  --dbg_dump_prop_clauses_file            -
% 3.24/1.00  --dbg_out_stat                          false
% 3.24/1.00  ------ Parsing...
% 3.24/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.24/1.00  
% 3.24/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.24/1.00  
% 3.24/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.24/1.00  
% 3.24/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.24/1.00  ------ Proving...
% 3.24/1.00  ------ Problem Properties 
% 3.24/1.00  
% 3.24/1.00  
% 3.24/1.00  clauses                                 33
% 3.24/1.00  conjectures                             3
% 3.24/1.00  EPR                                     2
% 3.24/1.00  Horn                                    29
% 3.24/1.00  unary                                   14
% 3.24/1.00  binary                                  5
% 3.24/1.00  lits                                    67
% 3.24/1.00  lits eq                                 28
% 3.24/1.00  fd_pure                                 0
% 3.24/1.00  fd_pseudo                               0
% 3.24/1.00  fd_cond                                 3
% 3.24/1.00  fd_pseudo_cond                          4
% 3.24/1.00  AC symbols                              0
% 3.24/1.00  
% 3.24/1.00  ------ Schedule dynamic 5 is on 
% 3.24/1.00  
% 3.24/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.24/1.00  
% 3.24/1.00  
% 3.24/1.00  ------ 
% 3.24/1.00  Current options:
% 3.24/1.00  ------ 
% 3.24/1.00  
% 3.24/1.00  ------ Input Options
% 3.24/1.00  
% 3.24/1.00  --out_options                           all
% 3.24/1.00  --tptp_safe_out                         true
% 3.24/1.00  --problem_path                          ""
% 3.24/1.00  --include_path                          ""
% 3.24/1.00  --clausifier                            res/vclausify_rel
% 3.24/1.00  --clausifier_options                    --mode clausify
% 3.24/1.00  --stdin                                 false
% 3.24/1.00  --stats_out                             all
% 3.24/1.00  
% 3.24/1.00  ------ General Options
% 3.24/1.00  
% 3.24/1.00  --fof                                   false
% 3.24/1.00  --time_out_real                         305.
% 3.24/1.00  --time_out_virtual                      -1.
% 3.24/1.00  --symbol_type_check                     false
% 3.24/1.00  --clausify_out                          false
% 3.24/1.00  --sig_cnt_out                           false
% 3.24/1.00  --trig_cnt_out                          false
% 3.24/1.00  --trig_cnt_out_tolerance                1.
% 3.24/1.00  --trig_cnt_out_sk_spl                   false
% 3.24/1.00  --abstr_cl_out                          false
% 3.24/1.00  
% 3.24/1.00  ------ Global Options
% 3.24/1.00  
% 3.24/1.00  --schedule                              default
% 3.24/1.00  --add_important_lit                     false
% 3.24/1.00  --prop_solver_per_cl                    1000
% 3.24/1.00  --min_unsat_core                        false
% 3.24/1.00  --soft_assumptions                      false
% 3.24/1.00  --soft_lemma_size                       3
% 3.24/1.00  --prop_impl_unit_size                   0
% 3.24/1.00  --prop_impl_unit                        []
% 3.24/1.00  --share_sel_clauses                     true
% 3.24/1.00  --reset_solvers                         false
% 3.24/1.00  --bc_imp_inh                            [conj_cone]
% 3.24/1.00  --conj_cone_tolerance                   3.
% 3.24/1.00  --extra_neg_conj                        none
% 3.24/1.00  --large_theory_mode                     true
% 3.24/1.00  --prolific_symb_bound                   200
% 3.24/1.00  --lt_threshold                          2000
% 3.24/1.00  --clause_weak_htbl                      true
% 3.24/1.00  --gc_record_bc_elim                     false
% 3.24/1.00  
% 3.24/1.00  ------ Preprocessing Options
% 3.24/1.00  
% 3.24/1.00  --preprocessing_flag                    true
% 3.24/1.00  --time_out_prep_mult                    0.1
% 3.24/1.00  --splitting_mode                        input
% 3.24/1.00  --splitting_grd                         true
% 3.24/1.00  --splitting_cvd                         false
% 3.24/1.00  --splitting_cvd_svl                     false
% 3.24/1.00  --splitting_nvd                         32
% 3.24/1.00  --sub_typing                            true
% 3.24/1.00  --prep_gs_sim                           true
% 3.24/1.00  --prep_unflatten                        true
% 3.24/1.00  --prep_res_sim                          true
% 3.24/1.00  --prep_upred                            true
% 3.24/1.00  --prep_sem_filter                       exhaustive
% 3.24/1.00  --prep_sem_filter_out                   false
% 3.24/1.00  --pred_elim                             true
% 3.24/1.00  --res_sim_input                         true
% 3.24/1.00  --eq_ax_congr_red                       true
% 3.24/1.00  --pure_diseq_elim                       true
% 3.24/1.00  --brand_transform                       false
% 3.24/1.00  --non_eq_to_eq                          false
% 3.24/1.00  --prep_def_merge                        true
% 3.24/1.00  --prep_def_merge_prop_impl              false
% 3.24/1.00  --prep_def_merge_mbd                    true
% 3.24/1.00  --prep_def_merge_tr_red                 false
% 3.24/1.00  --prep_def_merge_tr_cl                  false
% 3.24/1.00  --smt_preprocessing                     true
% 3.24/1.00  --smt_ac_axioms                         fast
% 3.24/1.00  --preprocessed_out                      false
% 3.24/1.00  --preprocessed_stats                    false
% 3.24/1.00  
% 3.24/1.00  ------ Abstraction refinement Options
% 3.24/1.00  
% 3.24/1.00  --abstr_ref                             []
% 3.24/1.00  --abstr_ref_prep                        false
% 3.24/1.00  --abstr_ref_until_sat                   false
% 3.24/1.00  --abstr_ref_sig_restrict                funpre
% 3.24/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.24/1.00  --abstr_ref_under                       []
% 3.24/1.00  
% 3.24/1.00  ------ SAT Options
% 3.24/1.00  
% 3.24/1.00  --sat_mode                              false
% 3.24/1.00  --sat_fm_restart_options                ""
% 3.24/1.00  --sat_gr_def                            false
% 3.24/1.00  --sat_epr_types                         true
% 3.24/1.00  --sat_non_cyclic_types                  false
% 3.24/1.00  --sat_finite_models                     false
% 3.24/1.00  --sat_fm_lemmas                         false
% 3.24/1.00  --sat_fm_prep                           false
% 3.24/1.00  --sat_fm_uc_incr                        true
% 3.24/1.00  --sat_out_model                         small
% 3.24/1.00  --sat_out_clauses                       false
% 3.24/1.00  
% 3.24/1.00  ------ QBF Options
% 3.24/1.00  
% 3.24/1.00  --qbf_mode                              false
% 3.24/1.00  --qbf_elim_univ                         false
% 3.24/1.00  --qbf_dom_inst                          none
% 3.24/1.00  --qbf_dom_pre_inst                      false
% 3.24/1.00  --qbf_sk_in                             false
% 3.24/1.00  --qbf_pred_elim                         true
% 3.24/1.00  --qbf_split                             512
% 3.24/1.00  
% 3.24/1.00  ------ BMC1 Options
% 3.24/1.00  
% 3.24/1.00  --bmc1_incremental                      false
% 3.24/1.00  --bmc1_axioms                           reachable_all
% 3.24/1.00  --bmc1_min_bound                        0
% 3.24/1.00  --bmc1_max_bound                        -1
% 3.24/1.00  --bmc1_max_bound_default                -1
% 3.24/1.00  --bmc1_symbol_reachability              true
% 3.24/1.00  --bmc1_property_lemmas                  false
% 3.24/1.00  --bmc1_k_induction                      false
% 3.24/1.00  --bmc1_non_equiv_states                 false
% 3.24/1.00  --bmc1_deadlock                         false
% 3.24/1.00  --bmc1_ucm                              false
% 3.24/1.00  --bmc1_add_unsat_core                   none
% 3.24/1.00  --bmc1_unsat_core_children              false
% 3.24/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.24/1.00  --bmc1_out_stat                         full
% 3.24/1.00  --bmc1_ground_init                      false
% 3.24/1.00  --bmc1_pre_inst_next_state              false
% 3.24/1.00  --bmc1_pre_inst_state                   false
% 3.24/1.00  --bmc1_pre_inst_reach_state             false
% 3.24/1.00  --bmc1_out_unsat_core                   false
% 3.24/1.00  --bmc1_aig_witness_out                  false
% 3.24/1.00  --bmc1_verbose                          false
% 3.24/1.00  --bmc1_dump_clauses_tptp                false
% 3.24/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.24/1.00  --bmc1_dump_file                        -
% 3.24/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.24/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.24/1.00  --bmc1_ucm_extend_mode                  1
% 3.24/1.00  --bmc1_ucm_init_mode                    2
% 3.24/1.00  --bmc1_ucm_cone_mode                    none
% 3.24/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.24/1.00  --bmc1_ucm_relax_model                  4
% 3.24/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.24/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.24/1.00  --bmc1_ucm_layered_model                none
% 3.24/1.00  --bmc1_ucm_max_lemma_size               10
% 3.24/1.00  
% 3.24/1.00  ------ AIG Options
% 3.24/1.00  
% 3.24/1.00  --aig_mode                              false
% 3.24/1.00  
% 3.24/1.00  ------ Instantiation Options
% 3.24/1.00  
% 3.24/1.00  --instantiation_flag                    true
% 3.24/1.00  --inst_sos_flag                         false
% 3.24/1.00  --inst_sos_phase                        true
% 3.24/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.24/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.24/1.00  --inst_lit_sel_side                     none
% 3.24/1.00  --inst_solver_per_active                1400
% 3.24/1.00  --inst_solver_calls_frac                1.
% 3.24/1.00  --inst_passive_queue_type               priority_queues
% 3.24/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.24/1.00  --inst_passive_queues_freq              [25;2]
% 3.24/1.00  --inst_dismatching                      true
% 3.24/1.00  --inst_eager_unprocessed_to_passive     true
% 3.24/1.00  --inst_prop_sim_given                   true
% 3.24/1.00  --inst_prop_sim_new                     false
% 3.24/1.00  --inst_subs_new                         false
% 3.24/1.00  --inst_eq_res_simp                      false
% 3.24/1.00  --inst_subs_given                       false
% 3.24/1.00  --inst_orphan_elimination               true
% 3.24/1.00  --inst_learning_loop_flag               true
% 3.24/1.00  --inst_learning_start                   3000
% 3.24/1.00  --inst_learning_factor                  2
% 3.24/1.00  --inst_start_prop_sim_after_learn       3
% 3.24/1.00  --inst_sel_renew                        solver
% 3.24/1.00  --inst_lit_activity_flag                true
% 3.24/1.00  --inst_restr_to_given                   false
% 3.24/1.00  --inst_activity_threshold               500
% 3.24/1.00  --inst_out_proof                        true
% 3.24/1.00  
% 3.24/1.00  ------ Resolution Options
% 3.24/1.00  
% 3.24/1.00  --resolution_flag                       false
% 3.24/1.00  --res_lit_sel                           adaptive
% 3.24/1.00  --res_lit_sel_side                      none
% 3.24/1.00  --res_ordering                          kbo
% 3.24/1.00  --res_to_prop_solver                    active
% 3.24/1.00  --res_prop_simpl_new                    false
% 3.24/1.00  --res_prop_simpl_given                  true
% 3.24/1.00  --res_passive_queue_type                priority_queues
% 3.24/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.24/1.00  --res_passive_queues_freq               [15;5]
% 3.24/1.00  --res_forward_subs                      full
% 3.24/1.00  --res_backward_subs                     full
% 3.24/1.00  --res_forward_subs_resolution           true
% 3.24/1.00  --res_backward_subs_resolution          true
% 3.24/1.00  --res_orphan_elimination                true
% 3.24/1.00  --res_time_limit                        2.
% 3.24/1.00  --res_out_proof                         true
% 3.24/1.00  
% 3.24/1.00  ------ Superposition Options
% 3.24/1.00  
% 3.24/1.00  --superposition_flag                    true
% 3.24/1.00  --sup_passive_queue_type                priority_queues
% 3.24/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.24/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.24/1.00  --demod_completeness_check              fast
% 3.24/1.00  --demod_use_ground                      true
% 3.24/1.00  --sup_to_prop_solver                    passive
% 3.24/1.00  --sup_prop_simpl_new                    true
% 3.24/1.00  --sup_prop_simpl_given                  true
% 3.24/1.00  --sup_fun_splitting                     false
% 3.24/1.00  --sup_smt_interval                      50000
% 3.24/1.00  
% 3.24/1.00  ------ Superposition Simplification Setup
% 3.24/1.00  
% 3.24/1.00  --sup_indices_passive                   []
% 3.24/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.24/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/1.00  --sup_full_bw                           [BwDemod]
% 3.24/1.00  --sup_immed_triv                        [TrivRules]
% 3.24/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.24/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/1.00  --sup_immed_bw_main                     []
% 3.24/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.24/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.24/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.24/1.00  
% 3.24/1.00  ------ Combination Options
% 3.24/1.00  
% 3.24/1.00  --comb_res_mult                         3
% 3.24/1.00  --comb_sup_mult                         2
% 3.24/1.00  --comb_inst_mult                        10
% 3.24/1.00  
% 3.24/1.00  ------ Debug Options
% 3.24/1.00  
% 3.24/1.00  --dbg_backtrace                         false
% 3.24/1.00  --dbg_dump_prop_clauses                 false
% 3.24/1.00  --dbg_dump_prop_clauses_file            -
% 3.24/1.00  --dbg_out_stat                          false
% 3.24/1.00  
% 3.24/1.00  
% 3.24/1.00  
% 3.24/1.00  
% 3.24/1.00  ------ Proving...
% 3.24/1.00  
% 3.24/1.00  
% 3.24/1.00  % SZS status Theorem for theBenchmark.p
% 3.24/1.00  
% 3.24/1.00   Resolution empty clause
% 3.24/1.00  
% 3.24/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.24/1.00  
% 3.24/1.00  fof(f22,conjecture,(
% 3.24/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 3.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f23,negated_conjecture,(
% 3.24/1.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 3.24/1.00    inference(negated_conjecture,[],[f22])).
% 3.24/1.00  
% 3.24/1.00  fof(f24,plain,(
% 3.24/1.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 3.24/1.00    inference(pure_predicate_removal,[],[f23])).
% 3.24/1.00  
% 3.24/1.00  fof(f41,plain,(
% 3.24/1.00    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 3.24/1.00    inference(ennf_transformation,[],[f24])).
% 3.24/1.00  
% 3.24/1.00  fof(f42,plain,(
% 3.24/1.00    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 3.24/1.00    inference(flattening,[],[f41])).
% 3.24/1.00  
% 3.24/1.00  fof(f53,plain,(
% 3.24/1.00    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1))) & k1_xboole_0 != sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_1(sK4))),
% 3.24/1.00    introduced(choice_axiom,[])).
% 3.24/1.00  
% 3.24/1.00  fof(f54,plain,(
% 3.24/1.00    ~r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1))) & k1_xboole_0 != sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_1(sK4)),
% 3.24/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f42,f53])).
% 3.24/1.00  
% 3.24/1.00  fof(f89,plain,(
% 3.24/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))),
% 3.24/1.00    inference(cnf_transformation,[],[f54])).
% 3.24/1.00  
% 3.24/1.00  fof(f3,axiom,(
% 3.24/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f62,plain,(
% 3.24/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.24/1.00    inference(cnf_transformation,[],[f3])).
% 3.24/1.00  
% 3.24/1.00  fof(f4,axiom,(
% 3.24/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f63,plain,(
% 3.24/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.24/1.00    inference(cnf_transformation,[],[f4])).
% 3.24/1.00  
% 3.24/1.00  fof(f5,axiom,(
% 3.24/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f64,plain,(
% 3.24/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.24/1.00    inference(cnf_transformation,[],[f5])).
% 3.24/1.00  
% 3.24/1.00  fof(f92,plain,(
% 3.24/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.24/1.00    inference(definition_unfolding,[],[f63,f64])).
% 3.24/1.00  
% 3.24/1.00  fof(f93,plain,(
% 3.24/1.00    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.24/1.00    inference(definition_unfolding,[],[f62,f92])).
% 3.24/1.00  
% 3.24/1.00  fof(f106,plain,(
% 3.24/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))),
% 3.24/1.00    inference(definition_unfolding,[],[f89,f93])).
% 3.24/1.00  
% 3.24/1.00  fof(f20,axiom,(
% 3.24/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f25,plain,(
% 3.24/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.24/1.00    inference(pure_predicate_removal,[],[f20])).
% 3.24/1.00  
% 3.24/1.00  fof(f39,plain,(
% 3.24/1.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.24/1.00    inference(ennf_transformation,[],[f25])).
% 3.24/1.00  
% 3.24/1.00  fof(f86,plain,(
% 3.24/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.24/1.00    inference(cnf_transformation,[],[f39])).
% 3.24/1.00  
% 3.24/1.00  fof(f12,axiom,(
% 3.24/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f30,plain,(
% 3.24/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.24/1.00    inference(ennf_transformation,[],[f12])).
% 3.24/1.00  
% 3.24/1.00  fof(f52,plain,(
% 3.24/1.00    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.24/1.00    inference(nnf_transformation,[],[f30])).
% 3.24/1.00  
% 3.24/1.00  fof(f75,plain,(
% 3.24/1.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.24/1.00    inference(cnf_transformation,[],[f52])).
% 3.24/1.00  
% 3.24/1.00  fof(f6,axiom,(
% 3.24/1.00    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 3.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f48,plain,(
% 3.24/1.00    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 3.24/1.00    inference(nnf_transformation,[],[f6])).
% 3.24/1.00  
% 3.24/1.00  fof(f49,plain,(
% 3.24/1.00    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 3.24/1.00    inference(flattening,[],[f48])).
% 3.24/1.00  
% 3.24/1.00  fof(f65,plain,(
% 3.24/1.00    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 3.24/1.00    inference(cnf_transformation,[],[f49])).
% 3.24/1.00  
% 3.24/1.00  fof(f102,plain,(
% 3.24/1.00    ( ! [X0,X1] : (k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))) )),
% 3.24/1.00    inference(definition_unfolding,[],[f65,f93,f93])).
% 3.24/1.00  
% 3.24/1.00  fof(f10,axiom,(
% 3.24/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f28,plain,(
% 3.24/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.24/1.00    inference(ennf_transformation,[],[f10])).
% 3.24/1.00  
% 3.24/1.00  fof(f73,plain,(
% 3.24/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.24/1.00    inference(cnf_transformation,[],[f28])).
% 3.24/1.00  
% 3.24/1.00  fof(f13,axiom,(
% 3.24/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f77,plain,(
% 3.24/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.24/1.00    inference(cnf_transformation,[],[f13])).
% 3.24/1.00  
% 3.24/1.00  fof(f16,axiom,(
% 3.24/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 3.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f33,plain,(
% 3.24/1.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.24/1.00    inference(ennf_transformation,[],[f16])).
% 3.24/1.00  
% 3.24/1.00  fof(f34,plain,(
% 3.24/1.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.24/1.00    inference(flattening,[],[f33])).
% 3.24/1.00  
% 3.24/1.00  fof(f80,plain,(
% 3.24/1.00    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.24/1.00    inference(cnf_transformation,[],[f34])).
% 3.24/1.00  
% 3.24/1.00  fof(f91,plain,(
% 3.24/1.00    ~r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1)))),
% 3.24/1.00    inference(cnf_transformation,[],[f54])).
% 3.24/1.00  
% 3.24/1.00  fof(f105,plain,(
% 3.24/1.00    ~r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)))),
% 3.24/1.00    inference(definition_unfolding,[],[f91,f93,f93])).
% 3.24/1.00  
% 3.24/1.00  fof(f21,axiom,(
% 3.24/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f40,plain,(
% 3.24/1.00    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.24/1.00    inference(ennf_transformation,[],[f21])).
% 3.24/1.00  
% 3.24/1.00  fof(f87,plain,(
% 3.24/1.00    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.24/1.00    inference(cnf_transformation,[],[f40])).
% 3.24/1.00  
% 3.24/1.00  fof(f14,axiom,(
% 3.24/1.00    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 3.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f31,plain,(
% 3.24/1.00    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.24/1.00    inference(ennf_transformation,[],[f14])).
% 3.24/1.00  
% 3.24/1.00  fof(f78,plain,(
% 3.24/1.00    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.24/1.00    inference(cnf_transformation,[],[f31])).
% 3.24/1.00  
% 3.24/1.00  fof(f2,axiom,(
% 3.24/1.00    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 3.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f43,plain,(
% 3.24/1.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.24/1.00    inference(nnf_transformation,[],[f2])).
% 3.24/1.00  
% 3.24/1.00  fof(f44,plain,(
% 3.24/1.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.24/1.00    inference(flattening,[],[f43])).
% 3.24/1.00  
% 3.24/1.00  fof(f45,plain,(
% 3.24/1.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.24/1.00    inference(rectify,[],[f44])).
% 3.24/1.00  
% 3.24/1.00  fof(f46,plain,(
% 3.24/1.00    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.24/1.00    introduced(choice_axiom,[])).
% 3.24/1.00  
% 3.24/1.00  fof(f47,plain,(
% 3.24/1.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.24/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f45,f46])).
% 3.24/1.00  
% 3.24/1.00  fof(f57,plain,(
% 3.24/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 3.24/1.00    inference(cnf_transformation,[],[f47])).
% 3.24/1.00  
% 3.24/1.00  fof(f98,plain,(
% 3.24/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 3.24/1.00    inference(definition_unfolding,[],[f57,f92])).
% 3.24/1.00  
% 3.24/1.00  fof(f109,plain,(
% 3.24/1.00    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_enumset1(X4,X4,X4,X1) != X2) )),
% 3.24/1.00    inference(equality_resolution,[],[f98])).
% 3.24/1.00  
% 3.24/1.00  fof(f110,plain,(
% 3.24/1.00    ( ! [X4,X1] : (r2_hidden(X4,k2_enumset1(X4,X4,X4,X1))) )),
% 3.24/1.00    inference(equality_resolution,[],[f109])).
% 3.24/1.00  
% 3.24/1.00  fof(f19,axiom,(
% 3.24/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)))),
% 3.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f37,plain,(
% 3.24/1.00    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.24/1.00    inference(ennf_transformation,[],[f19])).
% 3.24/1.00  
% 3.24/1.00  fof(f38,plain,(
% 3.24/1.00    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.24/1.00    inference(flattening,[],[f37])).
% 3.24/1.00  
% 3.24/1.00  fof(f85,plain,(
% 3.24/1.00    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.24/1.00    inference(cnf_transformation,[],[f38])).
% 3.24/1.00  
% 3.24/1.00  fof(f104,plain,(
% 3.24/1.00    ( ! [X0,X1] : (k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.24/1.00    inference(definition_unfolding,[],[f85,f93])).
% 3.24/1.00  
% 3.24/1.00  fof(f88,plain,(
% 3.24/1.00    v1_funct_1(sK4)),
% 3.24/1.00    inference(cnf_transformation,[],[f54])).
% 3.24/1.00  
% 3.24/1.00  fof(f11,axiom,(
% 3.24/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 3.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f29,plain,(
% 3.24/1.00    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 3.24/1.00    inference(ennf_transformation,[],[f11])).
% 3.24/1.00  
% 3.24/1.00  fof(f74,plain,(
% 3.24/1.00    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 3.24/1.00    inference(cnf_transformation,[],[f29])).
% 3.24/1.00  
% 3.24/1.00  fof(f103,plain,(
% 3.24/1.00    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 3.24/1.00    inference(definition_unfolding,[],[f74,f93])).
% 3.24/1.00  
% 3.24/1.00  fof(f15,axiom,(
% 3.24/1.00    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 3.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f32,plain,(
% 3.24/1.00    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 3.24/1.00    inference(ennf_transformation,[],[f15])).
% 3.24/1.00  
% 3.24/1.00  fof(f79,plain,(
% 3.24/1.00    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 3.24/1.00    inference(cnf_transformation,[],[f32])).
% 3.24/1.00  
% 3.24/1.00  fof(f18,axiom,(
% 3.24/1.00    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 3.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f35,plain,(
% 3.24/1.00    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.24/1.00    inference(ennf_transformation,[],[f18])).
% 3.24/1.00  
% 3.24/1.00  fof(f36,plain,(
% 3.24/1.00    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.24/1.00    inference(flattening,[],[f35])).
% 3.24/1.00  
% 3.24/1.00  fof(f83,plain,(
% 3.24/1.00    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.24/1.00    inference(cnf_transformation,[],[f36])).
% 3.24/1.00  
% 3.24/1.00  fof(f8,axiom,(
% 3.24/1.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f71,plain,(
% 3.24/1.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.24/1.00    inference(cnf_transformation,[],[f8])).
% 3.24/1.00  
% 3.24/1.00  fof(f7,axiom,(
% 3.24/1.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f50,plain,(
% 3.24/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.24/1.00    inference(nnf_transformation,[],[f7])).
% 3.24/1.00  
% 3.24/1.00  fof(f51,plain,(
% 3.24/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.24/1.00    inference(flattening,[],[f50])).
% 3.24/1.00  
% 3.24/1.00  fof(f70,plain,(
% 3.24/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.24/1.00    inference(cnf_transformation,[],[f51])).
% 3.24/1.00  
% 3.24/1.00  fof(f114,plain,(
% 3.24/1.00    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.24/1.00    inference(equality_resolution,[],[f70])).
% 3.24/1.00  
% 3.24/1.00  fof(f17,axiom,(
% 3.24/1.00    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f82,plain,(
% 3.24/1.00    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 3.24/1.00    inference(cnf_transformation,[],[f17])).
% 3.24/1.00  
% 3.24/1.00  fof(f1,axiom,(
% 3.24/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f55,plain,(
% 3.24/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.24/1.00    inference(cnf_transformation,[],[f1])).
% 3.24/1.00  
% 3.24/1.00  cnf(c_32,negated_conjecture,
% 3.24/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
% 3.24/1.00      inference(cnf_transformation,[],[f106]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1847,plain,
% 3.24/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) = iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_28,plain,
% 3.24/1.00      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.24/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1850,plain,
% 3.24/1.00      ( v4_relat_1(X0,X1) = iProver_top
% 3.24/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_2813,plain,
% 3.24/1.00      ( v4_relat_1(sK4,k2_enumset1(sK1,sK1,sK1,sK1)) = iProver_top ),
% 3.24/1.00      inference(superposition,[status(thm)],[c_1847,c_1850]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_18,plain,
% 3.24/1.00      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 3.24/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1857,plain,
% 3.24/1.00      ( v4_relat_1(X0,X1) != iProver_top
% 3.24/1.00      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 3.24/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_9,plain,
% 3.24/1.00      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
% 3.24/1.00      | k2_enumset1(X1,X1,X1,X1) = X0
% 3.24/1.00      | k1_xboole_0 = X0 ),
% 3.24/1.00      inference(cnf_transformation,[],[f102]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1863,plain,
% 3.24/1.00      ( k2_enumset1(X0,X0,X0,X0) = X1
% 3.24/1.00      | k1_xboole_0 = X1
% 3.24/1.00      | r1_tarski(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_4969,plain,
% 3.24/1.00      ( k2_enumset1(X0,X0,X0,X0) = k1_relat_1(X1)
% 3.24/1.00      | k1_relat_1(X1) = k1_xboole_0
% 3.24/1.00      | v4_relat_1(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top
% 3.24/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.24/1.00      inference(superposition,[status(thm)],[c_1857,c_1863]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_8021,plain,
% 3.24/1.00      ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK4)
% 3.24/1.00      | k1_relat_1(sK4) = k1_xboole_0
% 3.24/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.24/1.00      inference(superposition,[status(thm)],[c_2813,c_4969]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_15,plain,
% 3.24/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.24/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1860,plain,
% 3.24/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.24/1.00      | v1_relat_1(X1) != iProver_top
% 3.24/1.00      | v1_relat_1(X0) = iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_3900,plain,
% 3.24/1.00      ( v1_relat_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != iProver_top
% 3.24/1.00      | v1_relat_1(sK4) = iProver_top ),
% 3.24/1.00      inference(superposition,[status(thm)],[c_1847,c_1860]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_19,plain,
% 3.24/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.24/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1856,plain,
% 3.24/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_3909,plain,
% 3.24/1.00      ( v1_relat_1(sK4) = iProver_top ),
% 3.24/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_3900,c_1856]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_8485,plain,
% 3.24/1.00      ( k1_relat_1(sK4) = k1_xboole_0
% 3.24/1.00      | k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK4) ),
% 3.24/1.00      inference(global_propositional_subsumption,[status(thm)],[c_8021,c_3909]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_8486,plain,
% 3.24/1.00      ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK4)
% 3.24/1.00      | k1_relat_1(sK4) = k1_xboole_0 ),
% 3.24/1.00      inference(renaming,[status(thm)],[c_8485]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_22,plain,
% 3.24/1.00      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 3.24/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1853,plain,
% 3.24/1.00      ( k7_relat_1(X0,X1) = X0
% 3.24/1.00      | v4_relat_1(X0,X1) != iProver_top
% 3.24/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_3792,plain,
% 3.24/1.00      ( k7_relat_1(sK4,k2_enumset1(sK1,sK1,sK1,sK1)) = sK4
% 3.24/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.24/1.00      inference(superposition,[status(thm)],[c_2813,c_1853]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_3999,plain,
% 3.24/1.00      ( k7_relat_1(sK4,k2_enumset1(sK1,sK1,sK1,sK1)) = sK4 ),
% 3.24/1.00      inference(global_propositional_subsumption,[status(thm)],[c_3792,c_3909]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_8500,plain,
% 3.24/1.00      ( k7_relat_1(sK4,k1_relat_1(sK4)) = sK4 | k1_relat_1(sK4) = k1_xboole_0 ),
% 3.24/1.00      inference(superposition,[status(thm)],[c_8486,c_3999]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_30,negated_conjecture,
% 3.24/1.00      ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) ),
% 3.24/1.00      inference(cnf_transformation,[],[f105]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_36,plain,
% 3.24/1.00      ( r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_29,plain,
% 3.24/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.24/1.00      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.24/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_2169,plain,
% 3.24/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))
% 3.24/1.00      | k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,X0) = k9_relat_1(sK4,X0) ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_29]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_2237,plain,
% 3.24/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))
% 3.24/1.00      | k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3) = k9_relat_1(sK4,sK3) ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_2169]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_20,plain,
% 3.24/1.00      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 3.24/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_2594,plain,
% 3.24/1.00      ( r1_tarski(k9_relat_1(sK4,sK3),k2_relat_1(sK4)) | ~ v1_relat_1(sK4) ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_20]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_2596,plain,
% 3.24/1.00      ( r1_tarski(k9_relat_1(sK4,sK3),k2_relat_1(sK4)) = iProver_top
% 3.24/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_2594]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1378,plain,
% 3.24/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.24/1.00      theory(equality) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_2141,plain,
% 3.24/1.00      ( ~ r1_tarski(X0,X1)
% 3.24/1.00      | r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)))
% 3.24/1.00      | k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3) != X0
% 3.24/1.00      | k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) != X1 ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_1378]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_2236,plain,
% 3.24/1.00      ( r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)))
% 3.24/1.00      | ~ r1_tarski(k9_relat_1(sK4,sK3),X0)
% 3.24/1.00      | k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3) != k9_relat_1(sK4,sK3)
% 3.24/1.00      | k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) != X0 ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_2141]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_2595,plain,
% 3.24/1.00      ( r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)))
% 3.24/1.00      | ~ r1_tarski(k9_relat_1(sK4,sK3),k2_relat_1(sK4))
% 3.24/1.00      | k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3) != k9_relat_1(sK4,sK3)
% 3.24/1.00      | k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) != k2_relat_1(sK4) ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_2236]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_2598,plain,
% 3.24/1.00      ( k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3) != k9_relat_1(sK4,sK3)
% 3.24/1.00      | k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) != k2_relat_1(sK4)
% 3.24/1.00      | r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) = iProver_top
% 3.24/1.00      | r1_tarski(k9_relat_1(sK4,sK3),k2_relat_1(sK4)) != iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_2595]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_5,plain,
% 3.24/1.00      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
% 3.24/1.00      inference(cnf_transformation,[],[f110]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1867,plain,
% 3.24/1.00      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_8489,plain,
% 3.24/1.00      ( k1_relat_1(sK4) = k1_xboole_0
% 3.24/1.00      | r2_hidden(sK1,k1_relat_1(sK4)) = iProver_top ),
% 3.24/1.00      inference(superposition,[status(thm)],[c_8486,c_1867]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_27,plain,
% 3.24/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.24/1.00      | ~ v1_funct_1(X1)
% 3.24/1.00      | ~ v1_relat_1(X1)
% 3.24/1.00      | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ),
% 3.24/1.00      inference(cnf_transformation,[],[f104]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_33,negated_conjecture,
% 3.24/1.00      ( v1_funct_1(sK4) ),
% 3.24/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_325,plain,
% 3.24/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.24/1.00      | ~ v1_relat_1(X1)
% 3.24/1.00      | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
% 3.24/1.00      | sK4 != X1 ),
% 3.24/1.00      inference(resolution_lifted,[status(thm)],[c_27,c_33]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_326,plain,
% 3.24/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 3.24/1.00      | ~ v1_relat_1(sK4)
% 3.24/1.00      | k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0) ),
% 3.24/1.00      inference(unflattening,[status(thm)],[c_325]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1846,plain,
% 3.24/1.00      ( k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0)
% 3.24/1.00      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 3.24/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_326]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_9064,plain,
% 3.24/1.00      ( k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) = k11_relat_1(sK4,sK1)
% 3.24/1.00      | k1_relat_1(sK4) = k1_xboole_0
% 3.24/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.24/1.00      inference(superposition,[status(thm)],[c_8489,c_1846]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_16,plain,
% 3.24/1.00      ( ~ v1_relat_1(X0)
% 3.24/1.00      | k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
% 3.24/1.00      inference(cnf_transformation,[],[f103]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1859,plain,
% 3.24/1.00      ( k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1)
% 3.24/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_3911,plain,
% 3.24/1.00      ( k9_relat_1(sK4,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK4,X0) ),
% 3.24/1.00      inference(superposition,[status(thm)],[c_3909,c_1859]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_21,plain,
% 3.24/1.00      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 3.24/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1854,plain,
% 3.24/1.00      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 3.24/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_3912,plain,
% 3.24/1.00      ( k2_relat_1(k7_relat_1(sK4,X0)) = k9_relat_1(sK4,X0) ),
% 3.24/1.00      inference(superposition,[status(thm)],[c_3909,c_1854]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_4003,plain,
% 3.24/1.00      ( k9_relat_1(sK4,k2_enumset1(sK1,sK1,sK1,sK1)) = k2_relat_1(sK4) ),
% 3.24/1.00      inference(superposition,[status(thm)],[c_3999,c_3912]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_4287,plain,
% 3.24/1.00      ( k11_relat_1(sK4,sK1) = k2_relat_1(sK4) ),
% 3.24/1.00      inference(superposition,[status(thm)],[c_3911,c_4003]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_9065,plain,
% 3.24/1.00      ( k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) = k2_relat_1(sK4)
% 3.24/1.00      | k1_relat_1(sK4) = k1_xboole_0
% 3.24/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.24/1.00      inference(light_normalisation,[status(thm)],[c_9064,c_4287]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_9067,plain,
% 3.24/1.00      ( k1_relat_1(sK4) = k1_xboole_0 ),
% 3.24/1.00      inference(global_propositional_subsumption,
% 3.24/1.00                [status(thm)],
% 3.24/1.00                [c_8500,c_32,c_36,c_2237,c_2596,c_2598,c_3909,c_9065]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_26,plain,
% 3.24/1.00      ( ~ v1_relat_1(X0) | k1_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 3.24/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1851,plain,
% 3.24/1.00      ( k1_relat_1(X0) != k1_xboole_0
% 3.24/1.00      | k1_xboole_0 = X0
% 3.24/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_9257,plain,
% 3.24/1.00      ( sK4 = k1_xboole_0 | v1_relat_1(sK4) != iProver_top ),
% 3.24/1.00      inference(superposition,[status(thm)],[c_9067,c_1851]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_2270,plain,
% 3.24/1.00      ( ~ v1_relat_1(sK4)
% 3.24/1.00      | k1_relat_1(sK4) != k1_xboole_0
% 3.24/1.00      | k1_xboole_0 = sK4 ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_26]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_2276,plain,
% 3.24/1.00      ( k1_relat_1(sK4) != k1_xboole_0
% 3.24/1.00      | k1_xboole_0 = sK4
% 3.24/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_2270]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1376,plain,( X0 = X0 ),theory(equality) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_2285,plain,
% 3.24/1.00      ( sK4 = sK4 ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_1376]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1377,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_2435,plain,
% 3.24/1.00      ( X0 != X1 | sK4 != X1 | sK4 = X0 ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_1377]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_3551,plain,
% 3.24/1.00      ( X0 != sK4 | sK4 = X0 | sK4 != sK4 ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_2435]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_3552,plain,
% 3.24/1.00      ( sK4 != sK4 | sK4 = k1_xboole_0 | k1_xboole_0 != sK4 ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_3551]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_12977,plain,
% 3.24/1.00      ( sK4 = k1_xboole_0 ),
% 3.24/1.00      inference(global_propositional_subsumption,
% 3.24/1.00                [status(thm)],
% 3.24/1.00                [c_9257,c_32,c_36,c_2237,c_2276,c_2285,c_2596,c_2598,c_3552,
% 3.24/1.00                 c_3909,c_9065]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1849,plain,
% 3.24/1.00      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.24/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_2182,plain,
% 3.24/1.00      ( k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,X0) = k9_relat_1(sK4,X0) ),
% 3.24/1.00      inference(superposition,[status(thm)],[c_1847,c_1849]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1848,plain,
% 3.24/1.00      ( r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_2340,plain,
% 3.24/1.00      ( r1_tarski(k9_relat_1(sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
% 3.24/1.00      inference(demodulation,[status(thm)],[c_2182,c_1848]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_13008,plain,
% 3.24/1.00      ( r1_tarski(k9_relat_1(k1_xboole_0,sK3),k2_enumset1(k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1))) != iProver_top ),
% 3.24/1.00      inference(demodulation,[status(thm)],[c_12977,c_2340]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_13,plain,
% 3.24/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.24/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1862,plain,
% 3.24/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_2812,plain,
% 3.24/1.00      ( v4_relat_1(k1_xboole_0,X0) = iProver_top ),
% 3.24/1.00      inference(superposition,[status(thm)],[c_1862,c_1850]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_3791,plain,
% 3.24/1.00      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
% 3.24/1.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.24/1.00      inference(superposition,[status(thm)],[c_2812,c_1853]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_61,plain,
% 3.24/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_63,plain,
% 3.24/1.00      ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_61]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_2072,plain,
% 3.24/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.24/1.00      | v1_relat_1(X0)
% 3.24/1.00      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_15]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_2073,plain,
% 3.24/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.24/1.00      | v1_relat_1(X0) = iProver_top
% 3.24/1.00      | v1_relat_1(k2_zfmisc_1(X1,X2)) != iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_2072]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_2075,plain,
% 3.24/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 3.24/1.00      | v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
% 3.24/1.00      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_2073]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_2099,plain,
% 3.24/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_13]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_2102,plain,
% 3.24/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_2099]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_2104,plain,
% 3.24/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_2102]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_5652,plain,
% 3.24/1.00      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.24/1.00      inference(global_propositional_subsumption,
% 3.24/1.00                [status(thm)],
% 3.24/1.00                [c_3791,c_63,c_2075,c_2104]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_10,plain,
% 3.24/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.24/1.00      inference(cnf_transformation,[],[f114]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_2296,plain,
% 3.24/1.00      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.24/1.00      inference(superposition,[status(thm)],[c_10,c_1856]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_2802,plain,
% 3.24/1.00      ( k2_relat_1(k7_relat_1(k1_xboole_0,X0)) = k9_relat_1(k1_xboole_0,X0) ),
% 3.24/1.00      inference(superposition,[status(thm)],[c_2296,c_1854]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_5656,plain,
% 3.24/1.00      ( k9_relat_1(k1_xboole_0,X0) = k2_relat_1(k1_xboole_0) ),
% 3.24/1.00      inference(demodulation,[status(thm)],[c_5652,c_2802]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_23,plain,
% 3.24/1.00      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.24/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_5657,plain,
% 3.24/1.00      ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.24/1.00      inference(light_normalisation,[status(thm)],[c_5656,c_23]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_13015,plain,
% 3.24/1.00      ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1))) != iProver_top ),
% 3.24/1.00      inference(demodulation,[status(thm)],[c_13008,c_5657]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_0,plain,
% 3.24/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 3.24/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1872,plain,
% 3.24/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_14434,plain,
% 3.24/1.00      ( $false ),
% 3.24/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_13015,c_1872]) ).
% 3.24/1.00  
% 3.24/1.00  
% 3.24/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.24/1.00  
% 3.24/1.00  ------                               Statistics
% 3.24/1.00  
% 3.24/1.00  ------ General
% 3.24/1.00  
% 3.24/1.00  abstr_ref_over_cycles:                  0
% 3.24/1.00  abstr_ref_under_cycles:                 0
% 3.24/1.00  gc_basic_clause_elim:                   0
% 3.24/1.00  forced_gc_time:                         0
% 3.24/1.00  parsing_time:                           0.01
% 3.24/1.00  unif_index_cands_time:                  0.
% 3.24/1.00  unif_index_add_time:                    0.
% 3.24/1.00  orderings_time:                         0.
% 3.24/1.00  out_proof_time:                         0.012
% 3.24/1.00  total_time:                             0.419
% 3.24/1.00  num_of_symbols:                         53
% 3.24/1.00  num_of_terms:                           14913
% 3.24/1.00  
% 3.24/1.00  ------ Preprocessing
% 3.24/1.00  
% 3.24/1.00  num_of_splits:                          0
% 3.24/1.00  num_of_split_atoms:                     0
% 3.24/1.00  num_of_reused_defs:                     0
% 3.24/1.00  num_eq_ax_congr_red:                    28
% 3.24/1.00  num_of_sem_filtered_clauses:            1
% 3.24/1.00  num_of_subtypes:                        0
% 3.24/1.00  monotx_restored_types:                  0
% 3.24/1.00  sat_num_of_epr_types:                   0
% 3.24/1.00  sat_num_of_non_cyclic_types:            0
% 3.24/1.00  sat_guarded_non_collapsed_types:        0
% 3.24/1.00  num_pure_diseq_elim:                    0
% 3.24/1.00  simp_replaced_by:                       0
% 3.24/1.00  res_preprocessed:                       164
% 3.24/1.00  prep_upred:                             0
% 3.24/1.00  prep_unflattend:                        63
% 3.24/1.00  smt_new_axioms:                         0
% 3.24/1.00  pred_elim_cands:                        5
% 3.24/1.00  pred_elim:                              1
% 3.24/1.00  pred_elim_cl:                           1
% 3.24/1.00  pred_elim_cycles:                       7
% 3.24/1.00  merged_defs:                            0
% 3.24/1.00  merged_defs_ncl:                        0
% 3.24/1.00  bin_hyper_res:                          0
% 3.24/1.00  prep_cycles:                            4
% 3.24/1.00  pred_elim_time:                         0.015
% 3.24/1.00  splitting_time:                         0.
% 3.24/1.00  sem_filter_time:                        0.
% 3.24/1.00  monotx_time:                            0.
% 3.24/1.00  subtype_inf_time:                       0.
% 3.24/1.00  
% 3.24/1.00  ------ Problem properties
% 3.24/1.00  
% 3.24/1.00  clauses:                                33
% 3.24/1.00  conjectures:                            3
% 3.24/1.00  epr:                                    2
% 3.24/1.00  horn:                                   29
% 3.24/1.00  ground:                                 5
% 3.24/1.00  unary:                                  14
% 3.24/1.00  binary:                                 5
% 3.24/1.00  lits:                                   67
% 3.24/1.00  lits_eq:                                28
% 3.24/1.00  fd_pure:                                0
% 3.24/1.00  fd_pseudo:                              0
% 3.24/1.00  fd_cond:                                3
% 3.24/1.00  fd_pseudo_cond:                         4
% 3.24/1.00  ac_symbols:                             0
% 3.24/1.00  
% 3.24/1.00  ------ Propositional Solver
% 3.24/1.00  
% 3.24/1.00  prop_solver_calls:                      29
% 3.24/1.00  prop_fast_solver_calls:                 1239
% 3.24/1.00  smt_solver_calls:                       0
% 3.24/1.00  smt_fast_solver_calls:                  0
% 3.24/1.00  prop_num_of_clauses:                    5382
% 3.24/1.00  prop_preprocess_simplified:             16011
% 3.24/1.00  prop_fo_subsumed:                       18
% 3.24/1.00  prop_solver_time:                       0.
% 3.24/1.00  smt_solver_time:                        0.
% 3.24/1.00  smt_fast_solver_time:                   0.
% 3.24/1.00  prop_fast_solver_time:                  0.
% 3.24/1.00  prop_unsat_core_time:                   0.
% 3.24/1.00  
% 3.24/1.00  ------ QBF
% 3.24/1.00  
% 3.24/1.00  qbf_q_res:                              0
% 3.24/1.00  qbf_num_tautologies:                    0
% 3.24/1.00  qbf_prep_cycles:                        0
% 3.24/1.00  
% 3.24/1.00  ------ BMC1
% 3.24/1.00  
% 3.24/1.00  bmc1_current_bound:                     -1
% 3.24/1.00  bmc1_last_solved_bound:                 -1
% 3.24/1.00  bmc1_unsat_core_size:                   -1
% 3.24/1.00  bmc1_unsat_core_parents_size:           -1
% 3.24/1.00  bmc1_merge_next_fun:                    0
% 3.24/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.24/1.00  
% 3.24/1.00  ------ Instantiation
% 3.24/1.00  
% 3.24/1.00  inst_num_of_clauses:                    1747
% 3.24/1.00  inst_num_in_passive:                    1187
% 3.24/1.00  inst_num_in_active:                     513
% 3.24/1.00  inst_num_in_unprocessed:                47
% 3.24/1.00  inst_num_of_loops:                      560
% 3.24/1.00  inst_num_of_learning_restarts:          0
% 3.24/1.00  inst_num_moves_active_passive:          46
% 3.24/1.00  inst_lit_activity:                      0
% 3.24/1.00  inst_lit_activity_moves:                0
% 3.24/1.00  inst_num_tautologies:                   0
% 3.24/1.00  inst_num_prop_implied:                  0
% 3.24/1.00  inst_num_existing_simplified:           0
% 3.24/1.00  inst_num_eq_res_simplified:             0
% 3.24/1.00  inst_num_child_elim:                    0
% 3.24/1.00  inst_num_of_dismatching_blockings:      585
% 3.24/1.00  inst_num_of_non_proper_insts:           1506
% 3.24/1.00  inst_num_of_duplicates:                 0
% 3.24/1.00  inst_inst_num_from_inst_to_res:         0
% 3.24/1.00  inst_dismatching_checking_time:         0.
% 3.24/1.00  
% 3.24/1.00  ------ Resolution
% 3.24/1.00  
% 3.24/1.00  res_num_of_clauses:                     0
% 3.24/1.00  res_num_in_passive:                     0
% 3.24/1.00  res_num_in_active:                      0
% 3.24/1.00  res_num_of_loops:                       168
% 3.24/1.00  res_forward_subset_subsumed:            139
% 3.24/1.00  res_backward_subset_subsumed:           0
% 3.24/1.00  res_forward_subsumed:                   2
% 3.24/1.00  res_backward_subsumed:                  0
% 3.24/1.00  res_forward_subsumption_resolution:     0
% 3.24/1.00  res_backward_subsumption_resolution:    0
% 3.24/1.00  res_clause_to_clause_subsumption:       2658
% 3.24/1.00  res_orphan_elimination:                 0
% 3.24/1.00  res_tautology_del:                      41
% 3.24/1.00  res_num_eq_res_simplified:              0
% 3.24/1.00  res_num_sel_changes:                    0
% 3.24/1.00  res_moves_from_active_to_pass:          0
% 3.24/1.00  
% 3.24/1.00  ------ Superposition
% 3.24/1.00  
% 3.24/1.00  sup_time_total:                         0.
% 3.24/1.00  sup_time_generating:                    0.
% 3.24/1.00  sup_time_sim_full:                      0.
% 3.24/1.00  sup_time_sim_immed:                     0.
% 3.24/1.00  
% 3.24/1.00  sup_num_of_clauses:                     208
% 3.24/1.00  sup_num_in_active:                      49
% 3.24/1.00  sup_num_in_passive:                     159
% 3.24/1.00  sup_num_of_loops:                       110
% 3.24/1.00  sup_fw_superposition:                   166
% 3.24/1.00  sup_bw_superposition:                   238
% 3.24/1.00  sup_immediate_simplified:               131
% 3.24/1.00  sup_given_eliminated:                   0
% 3.24/1.00  comparisons_done:                       0
% 3.24/1.00  comparisons_avoided:                    113
% 3.24/1.00  
% 3.24/1.00  ------ Simplifications
% 3.24/1.00  
% 3.24/1.00  
% 3.24/1.00  sim_fw_subset_subsumed:                 37
% 3.24/1.00  sim_bw_subset_subsumed:                 9
% 3.24/1.00  sim_fw_subsumed:                        70
% 3.24/1.00  sim_bw_subsumed:                        2
% 3.24/1.00  sim_fw_subsumption_res:                 5
% 3.24/1.00  sim_bw_subsumption_res:                 0
% 3.24/1.00  sim_tautology_del:                      1
% 3.24/1.00  sim_eq_tautology_del:                   17
% 3.24/1.00  sim_eq_res_simp:                        1
% 3.24/1.00  sim_fw_demodulated:                     22
% 3.24/1.00  sim_bw_demodulated:                     57
% 3.24/1.00  sim_light_normalised:                   35
% 3.24/1.00  sim_joinable_taut:                      0
% 3.24/1.00  sim_joinable_simp:                      0
% 3.24/1.00  sim_ac_normalised:                      0
% 3.24/1.00  sim_smt_subsumption:                    0
% 3.24/1.00  
%------------------------------------------------------------------------------
